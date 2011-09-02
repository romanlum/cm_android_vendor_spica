#include <errno.h>
#include <pthread.h>
#include <fcntl.h>
#include <sys/epoll.h>
#include <math.h>
#include <time.h>
#include <dlfcn.h>
#include <semaphore.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <arpa/inet.h>

#include <termios.h>

#define  LOG_TAG  "gps_spica"
#include <cutils/log.h>
#include <cutils/sockets.h>
#include <hardware_legacy/gps.h>

#include "libsecril-client.h"

#define  GPS_DEVICE  "/dev/ttyGPS0"
//#define  GPS_DEBUG  0

#if GPS_DEBUG
#  define  D(...)   LOGD(__VA_ARGS__)
#else
#  define  D(...)   ((void)0)
#endif


#define GPS_STATUS_CB(_cb, _s)    \
  if ((_cb).status_cb) {          \
    GpsStatus gps_status;         \
    gps_status.status = (_s);     \
    (_cb).status_cb(&gps_status); \
    LOGD("gps status callback: 0x%x", _s); \
  }

//**************************** RILD ****************************
void                   *mSecRilLibHandle;
HRilClient              mRilClient;
HRilClient (*openClientRILD)  (void);
int        (*disconnectRILD)  (HRilClient);
int        (*closeClientRILD) (HRilClient);
int        (*isConnectedRILD) (HRilClient);
int        (*connectRILD)     (HRilClient);
int        (*registerUnsolicited)  (HRilClient,uint32_t,RilOnUnsolicited);
int        (*registerRequestComplete)  (HRilClient,uint32_t,RilOnComplete);
int        (*oemRequestRaw) (HRilClient, char *, size_t);

int         loadRILD();

int         gInitialized=0;

static void IntToByte(int64_t input,char output[8]);

//**************************** XTRA ****************************
GpsXtraCallbacks * spica_xtra_callbacks;
//**************************************************************

/* Nmea Parser stuff */

#define  NMEA_MAX_SIZE  83
enum {
  STATE_QUIT  = 0,
  STATE_INIT  = 1,
  STATE_START = 2
};

typedef struct {

    int     pos;
    int     overflow;
    int     utc_year;
    int     utc_mon;
    int     utc_day;
    int     utc_diff;
    GpsLocation  fix;
    GpsSvStatus  sv_status;
    int     sv_status_changed;
    char    in[ NMEA_MAX_SIZE+1 ];
gps_location_callback  callback;
} NmeaReader;

/* Since NMEA parser requires lcoks */

#define GPS_STATE_LOCK_FIX(_s)         \
{                                      \
  int ret;                             \
  do {                                 \
    ret = sem_wait(&(_s)->fix_sem);    \
  } while (ret < 0 && errno == EINTR);   \
}


#define GPS_STATE_UNLOCK_FIX(_s)       \
  sem_post(&(_s)->fix_sem)

typedef struct {
    int                     init;
    int                     fd;
    GpsCallbacks            callbacks;
    pthread_t               thread;
    pthread_t               tmr_thread;
    int                     control[2];
    int                     fix_freq;
    sem_t                   fix_sem;
    int                     first_fix;
    NmeaReader              reader;

} GpsState;



static GpsState  _gps_state[1];
static GpsState *gps_state = _gps_state;
static void *gps_timer_thread( void*  arg );





/*****************************************************************/
/*****************************************************************/
/*****                                                       *****/
/*****       N M E A   T O K E N I Z E R                     *****/
/*****                                                       *****/
/*****************************************************************/
/*****************************************************************/

typedef struct {
    const char*  p;
    const char*  end;
} Token;

#define  MAX_NMEA_TOKENS  16

typedef struct {
    int     count;
    Token   tokens[ MAX_NMEA_TOKENS ];
} NmeaTokenizer;

static int
nmea_tokenizer_init( NmeaTokenizer*  t, const char*  p, const char*  end )
{
    int    count = 0;
    char*  q;

    // the initial '$' is optional
    if (p < end && p[0] == '$')
        p += 1;

    // remove trailing newline
    if (end > p && end[-1] == '\n') {
        end -= 1;
        if (end > p && end[-1] == '\r')
            end -= 1;
    }

    // get rid of checksum at the end of the sentecne
    if (end >= p+3 && end[-3] == '*') {
        end -= 3;
    }

    while (p < end) {
        const char*  q = p;

        q =(const char *) memchr(p, ',', end-p);
        if (q == NULL)
            q = end;

        if (q > p) {
            if (count < MAX_NMEA_TOKENS) {
                t->tokens[count].p   = p;
                t->tokens[count].end = q;
                count += 1;
            }
        }
        if (q < end)
            q += 1;

        p = q;
    }

    t->count = count;
    return count;
}

static Token
nmea_tokenizer_get( NmeaTokenizer*  t, int  index )
{
    Token  tok;
    static const char*  dummy = "";

    if (index < 0 || index >= t->count) {
        tok.p = tok.end = dummy;
    } else
        tok = t->tokens[index];

    return tok;
}


static int
str2int( const char*  p, const char*  end )
{
    int   result = 0;
    int   len    = end - p;

    for ( ; len > 0; len--, p++ )
    {
        int  c;

        if (p >= end)
            goto Fail;

        c = *p - '0';
        if ((unsigned)c >= 10)
            goto Fail;

        result = result*10 + c;
    }
    return  result;

Fail:
    return -1;
}

static double
str2float( const char*  p, const char*  end )
{
    int   result = 0;
    int   len    = end - p;
    char  temp[16];

    if (len >= (int)sizeof(temp))
        return 0.;

    memcpy( temp, p, len );
    temp[len] = 0;
    return strtod( temp, NULL );
}

/*****************************************************************/
/*****************************************************************/
/*****                                                       *****/
/*****       N M E A   P A R S E R                           *****/
/*****                                                       *****/
/*****************************************************************/
/*****************************************************************/

#define  NMEA_MAX_SIZE  83


static void
nmea_reader_update_utc_diff( NmeaReader*  r )
{
    time_t         now = time(NULL);
    struct tm      tm_local;
    struct tm      tm_utc;
    long           time_local, time_utc;

    gmtime_r( &now, &tm_utc );
    localtime_r( &now, &tm_local );

    time_local = tm_local.tm_sec +
                 60*(tm_local.tm_min +
                 60*(tm_local.tm_hour +
                 24*(tm_local.tm_yday +
                 365*tm_local.tm_year)));

    time_utc = tm_utc.tm_sec +
               60*(tm_utc.tm_min +
               60*(tm_utc.tm_hour +
               24*(tm_utc.tm_yday +
               365*tm_utc.tm_year)));

    r->utc_diff = time_utc - time_local;
}


static void
nmea_reader_init( NmeaReader*  r )
{
    memset( r, 0, sizeof(*r) );

    r->pos      = 0;
    r->overflow = 0;
    r->utc_year = -1;
    r->utc_mon  = -1;
    r->utc_day  = -1;
    r->callback = NULL;

    nmea_reader_update_utc_diff( r );
}


static void
nmea_reader_set_callback( NmeaReader*  r, gps_location_callback  cb )
{
    r->callback = cb;
    if (cb != NULL && r->fix.flags != 0) {
        D("%s: sending latest fix to new callback", __FUNCTION__);
        r->callback( &r->fix );
        r->fix.flags = 0;
    }
}


static int
nmea_reader_update_time( NmeaReader*  r, Token  tok )
{
    int        hour, minute;
    double     seconds;
    struct tm  tm;
    time_t     fix_time;

    if (tok.p + 6 > tok.end)
        return -1;

    if (r->utc_year < 0) {
        // no date yet, get current one
        time_t  now = time(NULL);
        gmtime_r( &now, &tm );
        r->utc_year = tm.tm_year + 1900;
        r->utc_mon  = tm.tm_mon + 1;
        r->utc_day  = tm.tm_mday;
    }

    hour    = str2int(tok.p,   tok.p+2);
    minute  = str2int(tok.p+2, tok.p+4);
    seconds = str2float(tok.p+4, tok.end);

    tm.tm_hour  = hour;
    tm.tm_min   = minute;
    tm.tm_sec   = (int) seconds;
    tm.tm_year  = r->utc_year - 1900;
    tm.tm_mon   = r->utc_mon - 1;
    tm.tm_mday  = r->utc_day;
    tm.tm_isdst = -1;

    fix_time = mktime( &tm ) + r->utc_diff;
    r->fix.timestamp = (long long)fix_time * 1000;
    return 0;
}

static int
nmea_reader_update_date( NmeaReader*  r, Token  date, Token  time )
{
    Token  tok = date;
    int    day, mon, year;

    if (tok.p + 6 != tok.end) {
        D("date not properly formatted: '%.*s'", tok.end-tok.p, tok.p);
        return -1;
    }
    day  = str2int(tok.p, tok.p+2);
    mon  = str2int(tok.p+2, tok.p+4);
    year = str2int(tok.p+4, tok.p+6) + 2000;

    if ((day|mon|year) < 0) {
        D("date not properly formatted: '%.*s'", tok.end-tok.p, tok.p);
        return -1;
    }

    r->utc_year  = year;
    r->utc_mon   = mon;
    r->utc_day   = day;

    return nmea_reader_update_time( r, time );
}


static double
convert_from_hhmm( Token  tok )
{
    double  val     = str2float(tok.p, tok.end);
    int     degrees = (int)(floor(val) / 100);
    double  minutes = val - degrees*100.;
    double  dcoord  = degrees + minutes / 60.0;
    return dcoord;
}


static int
nmea_reader_update_latlong( NmeaReader*  r,
                            Token        latitude,
                            char         latitudeHemi,
                            Token        longitude,
                            char         longitudeHemi )
{
    double   lat, lon;
    Token    tok;

    tok = latitude;
    if (tok.p + 6 > tok.end) {
        D("latitude is too short: '%.*s'", tok.end-tok.p, tok.p);
        return -1;
    }
    lat = convert_from_hhmm(tok);
    if (latitudeHemi == 'S')
        lat = -lat;

    tok = longitude;
    if (tok.p + 6 > tok.end) {
        D("longitude is too short: '%.*s'", tok.end-tok.p, tok.p);
        return -1;
    }
    lon = convert_from_hhmm(tok);
    if (longitudeHemi == 'W')
        lon = -lon;

    r->fix.flags    |= GPS_LOCATION_HAS_LAT_LONG;
    r->fix.latitude  = lat;
    r->fix.longitude = lon;
    return 0;
}


static int
nmea_reader_update_altitude( NmeaReader*  r,
                             Token        altitude,
                             Token        units )
{
    double  alt;
    Token   tok = altitude;

    if (tok.p >= tok.end)
        return -1;

    r->fix.flags   |= GPS_LOCATION_HAS_ALTITUDE;
    r->fix.altitude = str2float(tok.p, tok.end);
    return 0;
}


static int
nmea_reader_update_bearing( NmeaReader*  r,
                            Token        bearing )
{
    double  alt;
    Token   tok = bearing;

    if (tok.p >= tok.end)
        return -1;

    r->fix.flags   |= GPS_LOCATION_HAS_BEARING;
    r->fix.bearing  = str2float(tok.p, tok.end);
    return 0;
}


static int
nmea_reader_update_speed( NmeaReader*  r,
                          Token        speed )
{
    double  alt;
    Token   tok = speed;

    if (tok.p >= tok.end)
        return -1;

    r->fix.flags   |= GPS_LOCATION_HAS_SPEED;
    r->fix.speed    = str2float(tok.p, tok.end);
    return 0;
}


static void
nmea_reader_parse( NmeaReader*  r )
{
   /* we received a complete sentence, now parse it to generate
    * a new GPS fix...
    */
    NmeaTokenizer  tzer[1];
    Token          tok;

    D("Received: '%.*s'", r->pos, r->in);
    if (r->pos < 9) {
        D("Too short. discarded.");
        return;
    }

    nmea_tokenizer_init(tzer, r->in, r->in + r->pos);
#if GPS_DEBUG
    {
        int  n;
        D("Found %d tokens", tzer->count);
        for (n = 0; n < tzer->count; n++) {
            Token  tok = nmea_tokenizer_get(tzer,n);
            D("%2d: '%.*s'", n, tok.end-tok.p, tok.p);
        }
    }
#endif

    tok = nmea_tokenizer_get(tzer, 0);
    if (tok.p + 5 > tok.end) {
        D("sentence id '%.*s' too short, ignored.", tok.end-tok.p, tok.p);
        return;
    }

    // ignore first two characters.
    tok.p += 2;
    if ( !memcmp(tok.p, "GGA", 3) ) {
        // GPS fix
        Token  tok_time          = nmea_tokenizer_get(tzer,1);
        Token  tok_latitude      = nmea_tokenizer_get(tzer,2);
        Token  tok_latitudeHemi  = nmea_tokenizer_get(tzer,3);
        Token  tok_longitude     = nmea_tokenizer_get(tzer,4);
        Token  tok_longitudeHemi = nmea_tokenizer_get(tzer,5);
        Token  tok_altitude      = nmea_tokenizer_get(tzer,9);
        Token  tok_altitudeUnits = nmea_tokenizer_get(tzer,10);

        nmea_reader_update_time(r, tok_time);
        nmea_reader_update_latlong(r, tok_latitude,
                                      tok_latitudeHemi.p[0],
                                      tok_longitude,
                                      tok_longitudeHemi.p[0]);
        nmea_reader_update_altitude(r, tok_altitude, tok_altitudeUnits);

    } else if ( !memcmp(tok.p, "GSA", 3) ) {
        // do something ?
    } else if ( !memcmp(tok.p, "RMC", 3) ) {
        Token  tok_time          = nmea_tokenizer_get(tzer,1);
        Token  tok_fixStatus     = nmea_tokenizer_get(tzer,2);
        Token  tok_latitude      = nmea_tokenizer_get(tzer,3);
        Token  tok_latitudeHemi  = nmea_tokenizer_get(tzer,4);
        Token  tok_longitude     = nmea_tokenizer_get(tzer,5);
        Token  tok_longitudeHemi = nmea_tokenizer_get(tzer,6);
        Token  tok_speed         = nmea_tokenizer_get(tzer,7);
        Token  tok_bearing       = nmea_tokenizer_get(tzer,8);
        Token  tok_date          = nmea_tokenizer_get(tzer,9);

        D("in RMC, fixStatus=%c", tok_fixStatus.p[0]);
        if (tok_fixStatus.p[0] == 'A')
        {
            nmea_reader_update_date( r, tok_date, tok_time );

            nmea_reader_update_latlong( r, tok_latitude,
                                           tok_latitudeHemi.p[0],
                                           tok_longitude,
                                           tok_longitudeHemi.p[0] );

            nmea_reader_update_bearing( r, tok_bearing );
            nmea_reader_update_speed  ( r, tok_speed );
        }
    } else {
        tok.p -= 2;
        D("unknown sentence '%.*s", tok.end-tok.p, tok.p);
    }
    if (r->fix.flags != 0) {
#if GPS_DEBUG
        char   temp[256];
        char*  p   = temp;
        char*  end = p + sizeof(temp);
        struct tm   utc;

        p += snprintf( p, end-p, "sending fix" );
        if (r->fix.flags & GPS_LOCATION_HAS_LAT_LONG) {
            p += snprintf(p, end-p, " lat=%g lon=%g", r->fix.latitude, r->fix.longitude);
        }
        if (r->fix.flags & GPS_LOCATION_HAS_ALTITUDE) {
            p += snprintf(p, end-p, " altitude=%g", r->fix.altitude);
        }
        if (r->fix.flags & GPS_LOCATION_HAS_SPEED) {
            p += snprintf(p, end-p, " speed=%g", r->fix.speed);
        }
        if (r->fix.flags & GPS_LOCATION_HAS_BEARING) {
            p += snprintf(p, end-p, " bearing=%g", r->fix.bearing);
        }
        if (r->fix.flags & GPS_LOCATION_HAS_ACCURACY) {
            p += snprintf(p,end-p, " accuracy=%g", r->fix.accuracy);
        }
        gmtime_r( (time_t*) &r->fix.timestamp, &utc );
        p += snprintf(p, end-p, " time=%s", asctime( &utc ) );
        D(temp);
#endif
        if (r->callback) {
            r->callback( &r->fix );
            r->fix.flags = 0;
        }
        else {
            D("no callback, keeping data until needed !");
        }
    }
}


static void
nmea_reader_addc( NmeaReader*  r, int  c )
{
    if (r->overflow) {
        r->overflow = (c != '\n');
        return;
    }

    if (r->pos >= (int) sizeof(r->in)-1 ) {
        r->overflow = 1;
        r->pos      = 0;
        return;
    }

    r->in[r->pos] = (char)c;
    r->pos       += 1;

    if (c == '\n') {
        nmea_reader_parse( r );
        r->pos = 0;
    }
}


/*****************************************************************/
/*****************************************************************/
/*****                                                       *****/
/*****       C O N N E C T I O N   S T A T E                 *****/
/*****                                                       *****/
/*****************************************************************/
/*****************************************************************/

static int gps_open_device(const char * device);
/* commands sent to the gps thread */
enum {
    CMD_QUIT  = 0,
    CMD_START = 1,
    CMD_STOP  = 2
};

static void
gps_state_done( GpsState*  s )
{
    // tell the thread to quit, and wait for it
    char   cmd = CMD_QUIT;
    void*  dummy;
    int ret;

    LOGD("gps send quit command");

    do { ret=write( s->control[0], &cmd, 1 ); }
    while (ret < 0 && errno == EINTR);

    LOGD("gps waiting for command thread to stop");

    pthread_join(s->thread, &dummy);

    /* Timer thread depends on this state check */
    s->init = STATE_QUIT;
    s->fix_freq = -1;

    // close the control socket pair
    close( s->control[0] ); s->control[0] = -1;
    close( s->control[1] ); s->control[1] = -1;

    // close connection to the QEMU GPS daemon
    close( s->fd ); s->fd = -1;

    sem_destroy(&s->fix_sem);

    memset(s, 0, sizeof(*s));

    LOGD("gps deinit complete");


}

static void
gps_state_start( GpsState*  s )
{
    char  cmd = CMD_START;
    int   ret;

    do { ret=write( s->control[0], &cmd, 1 ); }
    while (ret < 0 && errno == EINTR);

    if (ret != 1)
        LOGD("%s: could not send CMD_START command: ret=%d: %s",
          __FUNCTION__, ret, strerror(errno));
}


static void
gps_state_stop( GpsState*  s )
{
    char  cmd = CMD_STOP;
    int   ret;

    do { ret=write( s->control[0], &cmd, 1 ); }
    while (ret < 0 && errno == EINTR);

    if (ret != 1)
        LOGD("%s: could not send CMD_STOP command: ret=%d: %s",
          __FUNCTION__, ret, strerror(errno));
}

static int
epoll_register( int  epoll_fd, int  fd )
{
   struct epoll_event  ev;
    int                 ret, flags;

    /* important: make the fd non-blocking */
    flags = fcntl(fd, F_GETFL);
    fcntl(fd, F_SETFL, flags | O_NONBLOCK);

    ev.events  = EPOLLIN;
    ev.data.fd = fd;
    do {
        ret = epoll_ctl( epoll_fd, EPOLL_CTL_ADD, fd, &ev );
    } while (ret < 0 && errno == EINTR);
    return ret;
}


static int
epoll_deregister( int  epoll_fd, int  fd )
{
    int  ret;
    do {
        ret = epoll_ctl( epoll_fd, EPOLL_CTL_DEL, fd, NULL );
    } while (ret < 0 && errno == EINTR);
    return ret;
}

/* this is the main thread, it waits for commands from gps_state_start/stop and,

 * when started, messages from the QEMU GPS daemon. these are simple NMEA sentences

 * that must be parsed to be converted into GPS fixes sent to the framework

 */

static void*
gps_state_thread( void*  arg )
{
    GpsState*   state = (GpsState*) arg;
    NmeaReader  *reader;
    int         epoll_fd   = epoll_create(2);
    int         started    = 0;
    int         gps_fd     = state->fd;
    int         control_fd = state->control[1];

    reader = &state->reader;

    nmea_reader_init( reader );

    // register control file descriptors for polling
    epoll_register( epoll_fd, control_fd );
    epoll_register( epoll_fd, gps_fd );

    LOGD("gps thread running");

    GPS_STATUS_CB(state->callbacks, GPS_STATUS_ENGINE_ON);

    // now loop
    for (;;) {
        struct epoll_event   events[2];
        int                  ne, nevents;

        nevents = epoll_wait( epoll_fd, events, 2, -1 );
        if (nevents < 0) {
            if (errno != EINTR)
                LOGE("epoll_wait() unexpected error: %s", strerror(errno));
            continue;
        }
        D("gps thread received %d events", nevents);
        for (ne = 0; ne < nevents; ne++) {
            if ((events[ne].events & (EPOLLERR|EPOLLHUP)) != 0) {
                LOGE("EPOLLERR or EPOLLHUP after epoll_wait() !?");
                goto Exit;
            }
            if ((events[ne].events & EPOLLIN) != 0) {
                int  fd = events[ne].data.fd;

                if (fd == control_fd)
                {
                    char  cmd = 255;
                    int   ret;
                    D("gps control fd event");
                    do {
                        ret = read( fd, &cmd, 1 );
                    } while (ret < 0 && errno == EINTR);

                    if (cmd == CMD_QUIT) {
                        LOGD("gps thread quitting on demand");
                        goto Exit;
                    }
                    else if (cmd == CMD_START) {
                        if (!started) {
                            LOGD("gps thread starting  location_cb=%p", state->callbacks.location_cb);
                            started = 1;

                            
                            GPS_STATUS_CB(state->callbacks, GPS_STATUS_SESSION_BEGIN);

                            state->init = STATE_START;

                            if ( pthread_create( &state->tmr_thread, NULL, gps_timer_thread, state ) != 0 ) {
                                LOGE("could not create gps timer thread: %s", strerror(errno));
                                started = 0;
                                state->init = STATE_INIT;
                                goto Exit;
                            }

                        }
                    }
                    else if (cmd == CMD_STOP) {
                        if (started) {
                            void *dummy;
                            LOGD("gps thread stopping");
                            started = 0;

                            
                            state->init = STATE_INIT;

                            pthread_join(state->tmr_thread, &dummy);

                            GPS_STATUS_CB(state->callbacks, GPS_STATUS_SESSION_END);

                        }
                    }
                }
                else if (fd == gps_fd)
                {
                    char buf[512];
                    int  nn, ret;

                    do {
                        ret = read( fd, buf, sizeof(buf) );
                    } while (ret < 0 && errno == EINTR);

                    if (ret > 0)
                        for (nn = 0; nn < ret; nn++)
                            nmea_reader_addc( reader, buf[nn] );
                    D("gps fd event end");
                }
                else
                {
                    LOGE("epoll_wait() returned unkown fd %d ?", fd);
                }
            }
        }
    }
Exit:
    GPS_STATUS_CB(state->callbacks, GPS_STATUS_ENGINE_OFF);
    return NULL;
}



static void*

gps_timer_thread( void*  arg )
{

  GpsState *state = (GpsState *)arg;
  LOGD("gps entered timer thread");
  do {
    D("gps timer exp");
    GPS_STATE_LOCK_FIX(state);
    if (state->reader.fix.flags != 0) {
      D("gps fix cb: 0x%x", state->reader.fix.flags);
      if (state->callbacks.location_cb) {
          state->callbacks.location_cb( &state->reader.fix );
          state->reader.fix.flags = 0;
          state->first_fix = 1;
      }
      if (state->fix_freq == 0) {
        state->fix_freq = -1;
      }

    }

    if (state->reader.sv_status_changed != 0) {
      D("gps sv status callback");

      if (state->callbacks.sv_status_cb) {
          state->callbacks.sv_status_cb( &state->reader.sv_status );
          state->reader.sv_status_changed = 0;
      }

    }

    GPS_STATE_UNLOCK_FIX(state);
    sleep(state->fix_freq);
 
  } while(state->init == STATE_START);
  LOGD("gps timer thread destroyed");
  return NULL;

}
static void
gps_state_init( GpsState*  state )
{
    int    ret;
    int    done = 0;

    struct sigevent tmr_event;

    state->init       = STATE_INIT;
    state->control[0] = -1;
    state->control[1] = -1;
    state->fd         = -1;
    state->fix_freq   = 1;
    state->first_fix  = 0;

    if (sem_init(&state->fix_sem, 0, 1) != 0) {
      D("gps semaphore initialization failed! errno = %d", errno);
      return;
    }

    state->fd = gps_open_device(GPS_DEVICE);

    LOGD("gps will read from %s", GPS_DEVICE);
	 

    if ( socketpair( AF_LOCAL, SOCK_STREAM, 0, state->control ) < 0 ) {
        LOGE("could not create thread control socket pair: %s", strerror(errno));

        goto Fail;

    }

    if ( pthread_create( &state->thread, NULL, gps_state_thread, state ) != 0 ) {
        LOGE("could not create gps thread: %s", strerror(errno));
        goto Fail;
    }

    LOGD("gps state initialized");
    return;
Fail:

    gps_state_done( state );

}



static int
gps_open_device(const char * device)
{
	int fd;
	struct termios attr;
	speed_t speed=B4800;

	fd=open(device,O_RDONLY);

	if(fd<=0)
	{
		LOGE("could not open gps device %s", device);
		return -1;
	}
	
    if (tcgetattr(fd, &attr) < 0)
    {
        LOGE("error getting serial port settings!");
		close(fd); 
        return -1;
    }

    attr.c_cflag &= ~PARENB;  // no parity
    attr.c_cflag &= ~CSIZE;   // 8-bit bytes (first, clear mask, 
    attr.c_cflag |= CS8;      //              then, set value)
    cfmakeraw(&attr);
    attr.c_cflag |= CLOCAL;

	if (cfsetispeed(&attr, speed))
    {
        LOGE("cfsetispeed() error");
		close(fd); 
        return -1;
    }
    if (cfsetospeed(&attr, speed))
    {
        LOGE("cfsetospeed() error");
		close(fd); 
        return -1;  
    }
    
    attr.c_cc[VTIME]    = 100; // (100 * 0.1 sec) 10 second timeout
    attr.c_cc[VMIN]     = 0;   // 1 char satisfies read
    
    if (tcsetattr(fd, TCSANOW, &attr) < 0)
    {
        LOGE("error setting serial port settings");
        close(fd); 
        return -1;
    }

	return fd;

}



/*****************************************************************/
/*****************************************************************/
/*****                                                       *****/
/*****       I N T E R F A C E                               *****/
/*****                                                       *****/
/*****************************************************************/
/*****************************************************************/

static int
spica_gps_init(GpsCallbacks* callbacks)
{
	  GpsState*  s = _gps_state;
	  loadRILD();
	  LOGD("ConnectRILD: %d\n",connectRILD(mRilClient));	
	  
	  char initcmd[]={              0x0e, 0x04, 0xb5, 0x17, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x3c, 0x96,
                                 0xc8, 0x00, 0x00, 0x00, 0x00};
                                 
    LOGD("Initialize GPS: %d\n",oemRequestRaw(mRilClient, initcmd,181));
		if (!s->init)
        gps_state_init(s);

    if (s->fd < 0)
        return -1;

    s->callbacks = *callbacks;

    return 0;
}

static void
spica_gps_cleanup(void)
{
  GpsState*  s = _gps_state;
	char close_cmd[]={ 0x0e, 0x02, 0x03};
	LOGD("sent close cmd %d\n",oemRequestRaw(mRilClient, close_cmd,3)); 
    if (s->init)
        gps_state_done(s);

}


static int
spica_gps_start()
{
    GpsState*  s = _gps_state;
    char startcmd[]={ 0x0e,0x03,0x03};                             
    char initcmd[]={              0x0e, 0x04, 0xb5, 0x17, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x3c, 0x96,
                                 0xc8, 0x00, 0x00, 0x00, 0x00};
  
   
    LOGD("sent initCMD %d\n",oemRequestRaw(mRilClient, initcmd,181));
    sleep(1);
		LOGD("sent startCMD %d\n",oemRequestRaw(mRilClient, startcmd,3));
		
    if (!s->init) {
        D("%s: called with uninitialized state !!", __FUNCTION__);
        return -1;
    }

    
	
    D("%s: called", __FUNCTION__);
    gps_state_start(s);
    return 0;
}


static int
spica_gps_stop()
{
 
    char startcmd[]={ 0x0e, 0x06, 0x03};                             
    GpsState*  s = _gps_state;
    LOGD("sent stopCMD %d\n",oemRequestRaw(mRilClient, startcmd,3));
    
    
    if (!s->init) {
        LOGD("%s: called with uninitialized state !!", __FUNCTION__);
        return -1;
    }

    LOGD("%s: called", __FUNCTION__);
    gps_state_stop(s);
    
    return 0;
}


static int
spica_gps_inject_time(GpsUtcTime time, int64_t timeReference, int uncertainty)
{
    char timeArray[8];
    IntToByte(time,timeArray);
    char inject_time_request[]={  0x0e, 0x21, 0x12, timeArray[0], timeArray[1],timeArray[2], timeArray[3], timeArray[4], timeArray[5], timeArray[6], timeArray[7], 0x00, 0x00,
		0x00,0x00, 0x01, 0x00, 0x01, 0x00, 0x00};                              

    
    LOGD("sent injectTimeCMD %d\n",oemRequestRaw(mRilClient, inject_time_request,18));
    return 0;
}

static void IntToByte(int64_t input,char output[8])
{

	output[0] = (int) (input & 0x00000000000000FF);
	output[1] = (int) ((input >> 8) & 0x00000000000000FF);
	output[2] = (int) ((input >> 16) & 0x00000000000000FF);
	output[3] = (int) ((input >> 24) & 0x00000000000000FF);
	output[4] = (int) ((input >> 32) & 0x00000000000000FF);
	output[5] = (int) ((input >> 40) & 0x00000000000000FF);
	output[6] = (int) ((input >> 48) & 0x00000000000000FF);
	output[7] = (int) ((input >> 56) & 0x00000000000000FF);
	
}

static int
spica_gps_inject_location(double latitude, double longitude, float accuracy)
{
    
    return 0;
}

static void
spica_gps_delete_aiding_data(GpsAidingData flags)
{

}

static int spica_gps_set_position_mode(GpsPositionMode mode, int fix_frequency)
{
	  GpsState*  s = _gps_state;
    LOGD("Frequncy set to %d",fix_frequency);
    s->fix_freq = fix_frequency;
    return 0;
}





//*************************XTRA INTERFACE***********************************

int  spica_gps_xtra_init( GpsXtraCallbacks* callbacks )
{
	spica_xtra_callbacks=callbacks;
	return 0;
}

int  spica_gps_xtra_data( char* data, int length )
{
	int xtra_fd;
	int parts,len,i,lastlen;
	char xtradl[]={0x0e,0x23,0x04};
	char xtrainject[]={0x0e,0x22,0x04,0x01};
	int start=0;
	char header[]={0x00,0x04,0x00,0x27,0x01};
	
	GpsState*  s = _gps_state;
  if (!s->init) {
      LOGD("%s: called with uninitialized state !!", __FUNCTION__);
      return -1;
  }
	
	/*LOGD("XtraInject Request: %d\n",oemRequestRaw(mRilClient, xtradl,3));
	sleep(2);*/
	
  LOGD("XtraInject Request: %d\n",oemRequestRaw(mRilClient, xtrainject,4));
  
  sleep(2);
  usleep(0x186A0);
  
  
	LOGD("Injecting XTRA Data");
	
	parts=(length)/1024;
	if(length%1024==0)
		header[3]=parts;
	else
		header[3]=parts+1;
	
	
		
	LOGD("Injecting %d parts",header[3]);

  xtra_fd=open("/dev/ttyXTRA0",O_WRONLY|O_LARGEFILE);
	if(xtra_fd<0)
	{
		LOGE("error opening /dev/ttyXTRA0");
		return -1;
	}

	for(i=0;i<parts;i++)
	{	
		header[2]=i+1;
		LOGD("injecting part %d DATA[1]: 0x%x DATA[2]: 0x%x DATA[3]: 0x%x DATA[4]: 0x%x,DATA[4]: 0x%x",i+1,header[0],header[1],header[2],header[3],header[4]);

		len=write(xtra_fd,header,5);
		LOGD("written %d bytes",len);
		len=write(xtra_fd,data+start,1024);
		LOGD("written %d bytes",len);
		start+=1024;
		usleep(0xC350);
	}
        
	lastlen=(length)%1024;
	
	if(lastlen>0)
	{
		LOGD("injecting last part, length=%x",lastlen);
		header[2]=parts+1;
		header[0]=(lastlen) & 0xFF;
		header[1]=((lastlen) >> 8) & 0xFF;
	 LOGD("injecting last part %d DATA[1]: 0x%x DATA[2]: 0x%x DATA[3]: 0x%x DATA[4]: 0x%x,DATA[4]: 0x%x",parts+1,header[0],header[1],header[2],header[3],header[4]);
		write(xtra_fd,header,5);
		len=write(xtra_fd,data+start,lastlen);
		LOGD("written %d bytes",len);
		usleep(0xC350);
		
		
	}

	close(xtra_fd);
  LOGD("XTRA_INJECT");      
	return 0;

}

//******************EXTRA INTERFACE ********************
static const GpsXtraInterface spicaGpsXtraInterface = {
	  spica_gps_xtra_init,
	  spica_gps_xtra_data,
};
//*******************************************************

static const void*
spica_gps_get_extension(const char* name)
{
  LOGD("GET EXTENSION : %s",name);

	if(strcmp(GPS_XTRA_INTERFACE,name)==0)
	{
		LOGD("returning XTRA interface");
		return &spicaGpsXtraInterface;
	}

  return NULL;
}


static const GpsInterface  spicaGpsInterface = {
    spica_gps_init,
    spica_gps_start,
    spica_gps_stop,
    spica_gps_cleanup,
    spica_gps_inject_time,
    spica_gps_inject_location,
    spica_gps_delete_aiding_data,
    spica_gps_set_position_mode,
    spica_gps_get_extension,
};


const GpsInterface* gps_get_hardware_interface()
{
 LOGD("returning interface");
   return &spicaGpsInterface;
}


int loadRILD()
{
	mSecRilLibHandle = dlopen("libsecril-client.so", RTLD_NOW);

    if (mSecRilLibHandle) {
        LOGD("%s","libsecril-client.so is loaded");

        openClientRILD   = (HRilClient (*)(void))
                              dlsym(mSecRilLibHandle, "OpenClient_RILD");
        disconnectRILD   = (int (*)(HRilClient))
                              dlsym(mSecRilLibHandle, "Disconnect_RILD");
        closeClientRILD  = (int (*)(HRilClient))
                              dlsym(mSecRilLibHandle, "CloseClient_RILD");
        isConnectedRILD  = (int (*)(HRilClient))
                              dlsym(mSecRilLibHandle, "isConnected_RILD");
        connectRILD      = (int (*)(HRilClient))
                              dlsym(mSecRilLibHandle, "Connect_RILD");

        registerUnsolicited      = (int (*)(HRilClient,uint32_t,RilOnUnsolicited ))
                              dlsym(mSecRilLibHandle, "RegisterUnsolicitedHandler");

        registerRequestComplete      = (int (*)(HRilClient,uint32_t,RilOnComplete ))
                              dlsym(mSecRilLibHandle, "RegisterRequestCompleteHandler");
                              
        oemRequestRaw      = (int (*)(HRilClient client, char *data, size_t len))
                              dlsym(mSecRilLibHandle, "InvokeOemRequestHookRaw");

        if (!openClientRILD  || !disconnectRILD   || !closeClientRILD ||
            !isConnectedRILD || !connectRILD ||!registerUnsolicited || !registerRequestComplete || !oemRequestRaw)
        {
            LOGD("%s","Can't load all functions from libsecril-client.so");

            dlclose(mSecRilLibHandle);
            mSecRilLibHandle = NULL;
			
        } else {
            mRilClient = openClientRILD();
            if (mRilClient) {
				return 0;
			}
			else
			{
                LOGD("%s","OpenClient_RILD() error");

                dlclose(mSecRilLibHandle);
                mSecRilLibHandle = NULL;
				
            }
        }
    } else {
        LOGD("%s","Can't load libsecril-client.so");
	
    }
	return -1;
}







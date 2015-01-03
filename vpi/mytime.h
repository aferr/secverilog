#ifndef __MYTIME_H
#define __MYTIME_H

#define TIME_64

#ifndef TIME_RETURN_TYPE
#define TIME_RETURN_TYPE double
#endif

#ifdef F77_USE_UNDERSCORES
TIME_RETURN_TYPE cputime_msec_ ();
TIME_RETURN_TYPE realtime_msec_ ();
#else
TIME_RETURN_TYPE realtime_msec ();
TIME_RETURN_TYPE cputime_msec ();
#endif


/* Ticks */
#ifdef TIME_64
typedef unsigned long long Time_t;
#else
typedef unsigned int Time_t;
#endif

#define time_init(t)   do { t = 0; } while (0)
#define time_inc(t,v)  do { t += v; } while (0)
#define time_max(a,b)  ((a) > (b) ? (a) : (b))
#define time_min(a,b)  ((a) < (b) ? (a) : (b))
#define time_print(fp,t)  fprintf(fp,"%lu",(unsigned int)(t))
#define time_sprint(fp,t)  do { context_disable(); time_print (fp,t); context_enable (); } while (0)
#define time_add(t1,t2) ((t1)+(t2))

#endif

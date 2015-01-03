#ifndef __MIPS_IRIX5_H
#define __MIPS_IRIX5_H

#include "machine.h"

#define SYS_syscall	1000
#define SYS_exit	1001
#define SYS_fork	1002
#define SYS_read	1003
#define SYS_write	1004
#define SYS_open	1005
#define SYS_close	1006
#define SYS_creat	1008
#define SYS_link	1009
#define SYS_unlink	1010
#define SYS_execv	1011
#define SYS_chdir	1012
#define SYS_time	1013
#define SYS_chmod	1015
#define SYS_chown	1016
#define SYS_brk		1017
#define SYS_stat	1018
#define SYS_lseek	1019
#define SYS_getpid	1020
#define SYS_mount	1021
#define SYS_umount	1022
#define SYS_setuid	1023
#define SYS_getuid	1024
#define SYS_stime	1025
#define SYS_ptrace	1026
#define SYS_alarm	1027
#define SYS_pause	1029
#define SYS_utime	1030
#define SYS_access	1033
#define SYS_nice	1034
#define SYS_statfs	1035
#define SYS_sync	1036
#define SYS_kill	1037
#define SYS_fstatfs	1038
#define SYS_setpgrp	1039
#define	SYS_syssgi	1040
#define SYS_dup		1041
#define SYS_pipe	1042
#define SYS_times	1043
#define SYS_profil	1044
#define SYS_plock	1045
#define SYS_setgid	1046
#define SYS_getgid	1047
#define SYS_msgsys	1049
#define SYS_sysmips	1050
#define SYS_acct	1051
#define SYS_shmsys	1052
#define SYS_semsys	1053
#define SYS_ioctl	1054
#define SYS_uadmin	1055
#define SYS_sysmp	1056
#define SYS_utssys	1057
#define SYS_execve	1059
#define SYS_umask	1060
#define SYS_chroot	1061
#define SYS_fcntl	1062
#define SYS_ulimit	1063
#define SYS_rmdir	1079
#define SYS_mkdir	1080
#define SYS_getdents	1081
#define	SYS_sginap	1082
#define	SYS_sgikopt	1083
#define SYS_sysfs	1084
#define SYS_getmsg	1085
#define SYS_putmsg	1086
#define SYS_poll	1087
#define SYS_sigreturn	1088
#define SYS_accept	1089
#define SYS_bind	1090
#define SYS_connect	1091
#define SYS_gethostid	1092
#define SYS_getpeername	1093
#define SYS_getsockname	1094
#define SYS_getsockopt	1095
#define SYS_listen	1096
#define SYS_recv	1097
#define SYS_recvfrom	1098
#define SYS_recvmsg	1099
#define SYS_select	1100
#define SYS_send	1101
#define SYS_sendmsg	1102
#define SYS_sendto	1103
#define SYS_sethostid	1104
#define SYS_setsockopt	1105
#define SYS_shutdown	1106
#define SYS_socket	1107
#define SYS_gethostname	1108
#define SYS_sethostname	1109
#define SYS_getdomainname 1110
#define SYS_setdomainname 1111
#define SYS_truncate	1112
#define SYS_ftruncate	1113
#define SYS_rename	1114
#define	SYS_symlink	1115
#define	SYS_readlink	1116
#define	SYS_nfssvc	1119
#define	SYS_getfh	1120
#define	SYS_async_daemon 1121
#define	SYS_exportfs	1122
#define SYS_setregid	1123
#define SYS_setreuid	1124
#define SYS_getitimer	1125
#define SYS_setitimer	1126
#define	SYS_adjtime	1127
#define	SYS_BSD_getime	1128
#define	SYS_sproc	1129
#define	SYS_prctl	1130
#define	SYS_procblk	1131
#define	SYS_sprocsp	1132
#define	SYS_mmap	1134
#define	SYS_munmap	1135
#define	SYS_mprotect	1136
#define	SYS_msync	1137
#define	SYS_madvise	1138
#define	SYS_pagelock	1139
#define	SYS_getpagesize	1140
#define SYS_quotactl	1141
#define SYS_BSDgetpgrp	1143
#define SYS_BSDsetpgrp	1144
#define SYS_vhangup	1145
#define SYS_fsync	1146
#define SYS_fchdir	1147
#define SYS_getrlimit	1148
#define SYS_setrlimit	1149
#define SYS_cacheflush	1150
#define SYS_cachectl	1151
#define SYS_fchown	1152
#define SYS_fchmod	1153
#define SYS_socketpair	1155
#define SYS_sysinfo	1156
#define SYS_nuname	1157
#define SYS_xstat	1158
#define SYS_lxstat	1159
#define SYS_fxstat	1160
#define SYS_xmknod	1161
#define SYS_ksigaction	1162
#define SYS_sigpending	1163
#define SYS_sigprocmask	1164
#define SYS_sigsuspend	1165
#define SYS_sigpoll	1166
#define SYS_swapctl	1167
#define SYS_getcontext	1168
#define SYS_setcontext	1169
#define SYS_waitsys	1170
#define SYS_sigstack	1171
#define SYS_sigaltstack	1172
#define SYS_sigsendset	1173
#define SYS_statvfs	1174
#define SYS_fstatvfs	1175
#define SYS_getpmsg	1176
#define SYS_putpmsg	1177
#define SYS_lchown	1178
#define SYS_priocntl	1179
#define SYS_ksigqueue	1180

#define _ST_FSTYPSZ 16


typedef struct mips_timestruc {
#if BYTE_ORDER == BIG_ENDIAN
        int    tv_sec;         /* seconds */
        int    tv_nsec;        /* and nanoseconds */
#else
        int    tv_nsec;        /* and nanoseconds */
        int    tv_sec;         /* seconds */
#endif
} mips_timestruc_t;


struct  mips_stat {
#if BYTE_ORDER == SMALL_ENDIAN
        int    st_pad4[8];     /* expansion area */
        char    st_fstype[_ST_FSTYPSZ];
        int    st_blocks;  
        int    st_blksize;     
        mips_timestruc_t st_ctimespec; 
        mips_timestruc_t st_mtimespec;
        mips_timestruc_t st_atimespec; 
        int    st_pad3;        /* future off_t expansion */
        int    st_size;
        int    st_pad2[2];     /* dev and off_t expansion */
        dev_t   st_rdev;
        gid_t   st_gid;
        uid_t   st_uid;
        nlink_t st_nlink;
        mode_t  st_mode;
        ino_t   st_ino;
        int    st_pad1[3];     /* reserved for network id */
        dev_t   st_dev;
#else
        dev_t   st_dev; 
        int    st_pad1[3];     /* reserved for network id */
        ino_t   st_ino; 
        unsigned  st_mode;
        unsigned  st_nlink;
        uid_t   st_uid; 
        gid_t   st_gid; 
        dev_t   st_rdev;
        int    st_pad2[2];     /* dev and off_t expansion */
        unsigned   st_size;
        int    st_pad3;        /* future off_t expansion */
        mips_timestruc_t st_atimespec;
        mips_timestruc_t st_mtimespec;
        mips_timestruc_t st_ctimespec;
        int    st_blksize;
        int    st_blocks;
        char    st_fstype[_ST_FSTYPSZ];
        int    st_pad4[8];     /* expansion area */

#endif
};      


#define	SIM_FNDELAY		0x04	/* Non-blocking I/O */
#define	SIM_FAPPEND		0x08	/* append (writes guaranteed at the end) */
#define	SIM_FSYNC		0x10	/* synchronous write option */
#define	SIM_FNONBLOCK	0x80	/* Non-blocking I/O */
#define	SIM_FASYNC		0x1000	/* interrupt-driven I/O for sockets */
#define	SIM_FNONBLK		FNONBLOCK
#define	SIM_FDIRECT		0x8000

/*
 * open only modes
 */
#define	SIM_FCREAT	0x0100		/* create if nonexistent */
#define	SIM_FTRUNC	0x0200		/* truncate to zero length */
#define	SIM_FEXCL	0x0400		/* error if already created */
#define	SIM_FNOCTTY	0x0800		/* don't make this tty control term */

#define	SIM_O_RDONLY	0
#define	SIM_O_WRONLY	1
#define	SIM_O_RDWR		2
#define	SIM_O_NDELAY	0x04	/* non-blocking I/O */
#define	SIM_O_APPEND	0x08	/* append (writes guaranteed at the end) */
#define	SIM_O_SYNC		0x10	/* synchronous write option */
#define	SIM_O_NONBLOCK	0x80	/* non-blocking I/O (POSIX) */
#define SIM_O_DIRECT	0x8000	/* direct I/O */

#define	SIM_O_CREAT		0x100	/* open with file create (uses third open arg) */
#define	SIM_O_TRUNC		0x200	/* open with truncation */
#define	SIM_O_EXCL		0x400	/* exclusive open */
#define	SIM_O_NOCTTY	0x800	/* don't allocate controlling tty (POSIX) */

/* fcntl(2) requests */
#define	SIM_F_DUPFD		0	/* Duplicate fildes */
#define	SIM_F_GETFD		1	/* Get fildes flags */
#define	SIM_F_SETFD		2	/* Set fildes flags */
#define	SIM_F_GETFL		3	/* Get file flags */
#define	SIM_F_SETFL		4	/* Set file flags */

#define	SIM_F_GETLK		14	/* Get file lock */

#define	SIM_F_SETLK		6	/* Set file lock */
#define	SIM_F_SETLKW	7	/* Set file lock and wait */

#define	SIM_F_CHKFL		8	/* Unused */
#define	SIM_F_ALLOCSP	10	/* Reserved */
#define	SIM_F_FREESP	11	/* Free file space */

#define	SIM_F_SETBSDLK	12	/* Set Berkeley record lock */
#define	SIM_F_SETBSDLKW	13	/* Set Berkeley record lock and wait */
#define	SIM_F_DIOINFO	30	/* get direct I/O parameters */
#define	SIM_F_FSGETXATTR	31	/* get extended file attributes (xFS) */
#define	SIM_F_FSSETXATTR	32	/* set extended file attributes (xFS) */
#define	SIM_F_GETLK64	33	/* Get 64 bit file lock */
#define	SIM_F_SETLK64	34	/* Set 64 bit file lock */
#define	SIM_F_SETLKW64	35	/* Set 64 bit file lock and wait */
#define	SIM_F_ALLOCSP64	36	/* Alloc 64 bit file space */
#define	SIM_F_FREESP64	37	/* Free 64 bit file space */
#define	SIM_F_GETBMAP	38	/* Get block map (64 bit only) */
#define	SIM_F_FSSETDM	39	/* Set DMI event mask and state (XFS only) */

#define SIM_F_RSETLK	20	/* Remote SETLK for NFS */
#define SIM_F_RGETLK	21	/* Remote GETLK for NFS */
#define SIM_F_RSETLKW	22	/* Remote SETLKW for NFS */

/* only for sockets */
#define	SIM_F_GETOWN	23	/* Get owner (socket emulation) */
#define	SIM_F_SETOWN	24	/* Set owner (socket emulation) */

/*
 * File segment locking types.
 */
#define	SIM_F_RDLCK	01	/* Read lock */
#define	SIM_F_WRLCK	02	/* Write lock */
#define	SIM_F_UNLCK	03	/* Remove lock(s) */

/*
 * POSIX constants 
 */

#define	SIM_O_ACCMODE	3	/* Mask for file access modes */
#define	SIM_FD_CLOEXEC	1	/* close on exec flag */


/*
 *
 * sysmp.h
 *
 */

/* possible opcodes */
#define SIM_MP_NPROCS       1       /* # processor in complex */
#define SIM_MP_NAPROCS      2       /* # active processors in complex */
#define SIM_MP_ENABLE       4       /* enable a processor OBSOLETE */
#define SIM_MP_DISABLE      5       /* disable a processor OBSOLETE */
#define SIM_MP_KERNADDR     8       /* get address of kernel structure */
#define SIM_MP_SASZ         9
#define SIM_MP_SAGET        10      /* get system activity for all cpus summed */
#define SIM_MP_SCHED        13      /* scheduler control calls */
#define SIM_MP_PGSIZE       14      /* get system page size */
#define SIM_MP_SAGET1       15      /* get system activity for a single CPU */
#define SIM_MP_EMPOWER      16      /* allow processor to sched any process */
#define SIM_MP_RESTRICT     17      /* restrict processor to mustrun processes */
#define SIM_MP_CLOCK        18      /* processor becomes (software) clock handler */
#define SIM_MP_MUSTRUN      19      /* assign process to this processor */
#define SIM_MP_RUNANYWHERE  20      /* let process run on any processor (default) */
#define SIM_MP_STAT         21      /* return processor status */
#define SIM_MP_ISOLATE      22      /* isolate a processor from inter-cpu intr */
#define SIM_MP_UNISOLATE    23      /* un-isolate a processor */
#define SIM_MP_PREEMPTIVE   24      /* turn clock back on an isolated processor */
#define SIM_MP_NONPREEMPTIVE  25    /* turn clock off of an isolated processor */
#define SIM_MP_FASTCLOCK    26      /* cpu becomes the sw fast clock handler */
#define SIM_MP_PSET         27      /* manipulate a processor set */
#define SIM_MP_CLEARNFSSTAT 28      /* clear nfsstat */
#define SIM_MP_GETMUSTRUN   29      /* return current mustrun for current process */

#define SIM_TCGETA 0x5401

#endif

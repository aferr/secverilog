#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <sys/time.h>
#include <signal.h>
#include "syscall.h"
#include "misc.h"
#include "mips-irix5.h"
#include "unistd.h"
#include "asm-mips/mips-linux-syscalls.h" // This is from the linux-threads directory of sescutils
//#include <sys/syscall.h>
//#include <unistd.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/file.h>
#include <sys/uio.h>
#include <sys/times.h>
#include <sys/socket.h>
#include "vpi_user.h"
#include <errno.h>
#include <stdint.h>

extern Mem *physical_memory;
extern SysCall *syscall_iface;
// map open(), creat() flags from host architecture to native
// architecture
static unsigned int mode_remap (unsigned int);

#define MINUS_ONE  0xffffffffffffffffULL

#define UNIX_RETURN(x) 				\
   do { 					\
     /*vpi_printf("Returning 0x%08x\n  %llx\n",x,x);*/	\
     SetReg(REG_V0, x);				\
     if (((signed)GetReg(REG_V0)) < 0) { 	\
       SetReg(REG_A3,1);			\
       SetReg(REG_V0, errno); 			\
     } 						\
     else { 					\
       SetReg(REG_A3,0);			\
     } 						\
     return;					\
   } while (0)


void WriteByte (LL addr, unsigned char byte) {
  LL value;
  
  value = GetDWord (addr);
  value = BESetByte (addr, value, byte);
  SetDWord (addr, value);
}

unsigned char ReadByte (LL addr) {
  LL value;
  
  value = GetDWord (addr);
  return BEGetByte (addr, value);
}

void WriteWord (LL addr, Word w) {
  SetWord (addr, w);
}

Word ReadWord (LL addr) {
  return GetWord (addr);
}

void WriteHalf (LL addr, Word w) {
  LL value;
  
  value = GetDWord (addr);
  value = BESetHalfWord (addr, value, w);
  SetDWord (addr, value);
}

Word ReadHalf (LL addr) {
  LL value;
  
  value = GetDWord (addr);
  return BEGetHalfWord (addr, value);
}


/*------------------------------------------------------------------------
 *
 * system call emulation
 *
 *------------------------------------------------------------------------
 */

SysCall *new_SysCall (void) 
{
  int i;
  SysCall *newsc;

  newsc = (SysCall *) malloc(sizeof(SysCall));
  Assert(newsc, "What?!?");
  
  for (i=0; i < 256; i++)
    newsc->_fdlist[i] = -1;
  
  // open file descriptors
  newsc->_fdlist[0] = 0;
  newsc->_fdlist[1] = 1;
  newsc->_fdlist[2] = 2;
  newsc->_argc = 0;
  newsc->_reg[0] = 0;

  return newsc;
}

void kill_SysCall (SysCall *sc)
{
  int i;

  for (i=0; i < sc->_argc; i++)
    FREE (sc->_argv[i]);
  if (sc->_argc)
    FREE (sc->_argv);
}

void Reset (SysCall *sc)
{
  int i;

  for (i=3; i < 256; i++) {
    if (sc->_fdlist[i] > 0) {
      close (sc->_fdlist[i]);
      sc->_fdlist[i] = -1;
    }
  }
}

void ArgumentSetup (SysCall *sc, int argc, char **argv, LL addr)
{
  int i;
  Assert (argc > 0, "SysCall_ArgumentSetup: argc not positive?!");

  if (sc->_argc) {
    for (i=0; i < sc->_argc; i++)
      FREE (sc->_argv[i]);
    if (sc->_argc)
      FREE (sc->_argv);
  }
  sc->_argc = argc;
  MALLOC (sc->_argv, char *, sc->_argc);
  for (i=0; i < sc->_argc; i++) {
    sc->_argv[i] = Strdup (argv[i]);
  }
  sc->_argaddr = addr;
}


char *SysCallName (int num)
{
  switch (num) {
    // Checking through this list by hand to make sure it is correct
    /* This case is commented out to prevent a duplicate btw __mipseb_linux_Linux and __mipseb_linux_syscall
       case __mipseb_linux_Linux:
       return "Linux";
       break;
    */
  case __mipseb_linux_syscall:
    return "syscall";
    break;
 case __mipseb_linux_exit:
    return "exit";
    break;
  case __mipseb_linux_fork:
    return "fork";
    break;
  case __mipseb_linux_read:
    return "read";
    break;
  case __mipseb_linux_write:
    return "write";
    break;
  case __mipseb_linux_open:
    return "open";
    break;
  case __mipseb_linux_close:
    return "close";
    break;
  case __mipseb_linux_waitpid:
    return "waitpid";
    break;
  case __mipseb_linux_creat:
    return "creat";
    break;
  case __mipseb_linux_link:
    return "link";
    break;
  case __mipseb_linux_unlink:
    return "unlink";
    break;
  case __mipseb_linux_execve:
    return "execve";
    break;
  case __mipseb_linux_chdir:
    return "chdir";
    break;
  case __mipseb_linux_time:
    return "time";
    break;
  case __mipseb_linux_mknod:
    return "mknod";
    break;
  case __mipseb_linux_chmod:
    return "chmod";
    break;
  case __mipseb_linux_lchown:
    return "lchown";
    break;
  case __mipseb_linux_break:
    return "break";
    break;
  case __mipseb_linux_oldstat:
    return "oldstat";
    break;
  case __mipseb_linux_lseek:
    return "lseek";
    break;
  case __mipseb_linux_getpid:
    return "getpid";
    break;
  case __mipseb_linux_mount:
    return "mount";
    break;
  case __mipseb_linux_umount:
    return "umount";
    break;
  case __mipseb_linux_setuid:
    return "setuid";
    break;
  case __mipseb_linux_getuid:
    return "getuid";
    break;
  case __mipseb_linux_stime:
    return "stime";
    break;
  case __mipseb_linux_ptrace:
    return "ptrace";
    break;
  case __mipseb_linux_alarm:
    return "alarm";
    break;
  case __mipseb_linux_oldfstat:
    return "oldfstat";
    break;
  case __mipseb_linux_pause:
    return "pause";
    break;
  case __mipseb_linux_utime:
    return "utime";
    break;
  case __mipseb_linux_stty:
    return "stty";
    break;
  case __mipseb_linux_gtty:
    return "gtty";
    break;
  case __mipseb_linux_access:
    return "access";
    break;
  case __mipseb_linux_nice:
    return "nice";
    break;
  case __mipseb_linux_ftime:
    return "ftime";
    break;
  case __mipseb_linux_sync:
    return "sync";
    break;
  case __mipseb_linux_kill:
    return "kill";
    break; 
  case __mipseb_linux_rename:
    return "rename";
    break;
  case __mipseb_linux_mkdir:
    return "mkdir";
    break;
  case __mipseb_linux_rmdir:
    return "rmdir";
    break;
  case __mipseb_linux_dup:
    return "dup";
    break;
  case __mipseb_linux_pipe:
    return "pipe";
    break;
  case __mipseb_linux_times:
    return "times";
    break;
  case __mipseb_linux_prof:
    return "prof";
    break;
  case __mipseb_linux_brk:
    return "brk";
    break;
  case __mipseb_linux_setgid:
    return "setgid";
    break;
  case __mipseb_linux_getgid:
    return "getgid";
    break;
  case __mipseb_linux_signal:
    return "signal";
    break;
  case __mipseb_linux_geteuid:
    return "geteuid";
    break;
  case __mipseb_linux_getegid:
    return "getegid";
    break;
  case __mipseb_linux_acct:
    return "acct";
    break;
  case __mipseb_linux_umount2:
    return "umount2";
    break;
  case __mipseb_linux_lock:
    return "lock";
    break;
  case __mipseb_linux_ioctl:
    return "ioctl";
    break;
  case __mipseb_linux_fcntl:
    return "fcntl";
    break;
  case __mipseb_linux_mpx:
    return "mpx";
    break;
  case __mipseb_linux_setpgid:
    return "setpgid";
    break;
  case __mipseb_linux_ulimit:
    return "ulimit";
    break;
  case __mipseb_linux_unused59:
    return "unused59";
    break;
  case __mipseb_linux_umask:
    return "umask";
    break;
  case __mipseb_linux_chroot:
    return "chroot";
    break;
  case __mipseb_linux_ustat:
    return "ustat";
    break;
  case __mipseb_linux_dup2:
    return "dup2";
    break;
  case __mipseb_linux_getppid:
    return "getppid";
    break;
  case __mipseb_linux_getpgrp:
    return "getpgrp";
    break;
  case __mipseb_linux_setsid:
    return "setsid";
    break;
  case __mipseb_linux_sigaction:
    return "sigaction";
    break;
  case __mipseb_linux_sgetmask:
    return "sgetmask";
    break;
  case __mipseb_linux_ssetmask:
    return "ssetmask";
    break;
  case __mipseb_linux_setreuid:
    return "setreuid";
    break;
  case __mipseb_linux_setregid:
    return "setregid";
    break;
  case __mipseb_linux_sigsuspend:
    return "sigsuspend";
    break;
  case __mipseb_linux_sigpending:
    return "sigpending";
    break;
  case __mipseb_linux_sethostname:
    return "sethostname";
    break;
  case __mipseb_linux_setrlimit:
    return "setrlimit";
    break;
  case __mipseb_linux_getrlimit:
    return "getrlimit";
    break;
  case __mipseb_linux_getrusage:
    return "getrusage";
    break;
  case __mipseb_linux_gettimeofday:
    return "gettimeofday";
    break;
  case __mipseb_linux_settimeofday:
    return "settimeofday";
    break;
  case __mipseb_linux_getgroups:
    return "getgroups";
    break;
  case __mipseb_linux_setgroups:
    return "setgroups";
    break;
  case __mipseb_linux_reserved82:
    return "reserved82";
    break;
  case __mipseb_linux_symlink:
    return "symlink";
    break;
  case __mipseb_linux_oldlstat:
    return "oldlstat";
    break;
  case __mipseb_linux_readlink:
    return "readlink";
    break;
  case __mipseb_linux_uselib:
    return "uselib";
    break;
  case __mipseb_linux_swapon:
    return "swapon";
    break;
  case __mipseb_linux_reboot:
    return "reboot";
    break;
  case __mipseb_linux_readdir:
    return "readdir";
    break;
  case __mipseb_linux_mmap:
    return "mmap";
    break;
  case __mipseb_linux_munmap:
    return "munmap";
    break;
  case __mipseb_linux_truncate:
    return "truncate";
    break;
  case __mipseb_linux_ftruncate:
    return "ftuncate";
    break;
  case __mipseb_linux_fchmod:
    return "fchmod";
    break;
  case __mipseb_linux_fchown:
    return "fchown";
    break;
  case __mipseb_linux_getpriority:
    return "getpriority";
    break;
  case __mipseb_linux_setpriority:
    return "setpriority";
    break;
  case __mipseb_linux_profil:
    return "profil";
    break;
  case __mipseb_linux_statfs:
    return "statfs";
    break;
  case __mipseb_linux_fstatfs:
    return "fstatfs";
    break;
  case __mipseb_linux_ioperm:
    return "ioperm";
    break;
  case __mipseb_linux_socketcall:
    return "socketcall";
    break;
  case __mipseb_linux_syslog:
    return "syslog";
    break;
  case __mipseb_linux_setitimer:
    return "setitimer";
    break;
  case __mipseb_linux_getitimer:
    return "getitimer";
    break;
  case __mipseb_linux_stat:
    return "stat";
    break;
  case __mipseb_linux_lstat:
    return "lstat";
    break;
  case __mipseb_linux_fstat:
    return "fstat";
    break;
  case __mipseb_linux_unused109:
    return "unused109";
    break;
  case __mipseb_linux_iopl:
    return "iopl";
    break;
 case __mipseb_linux_vhangup:
    return "vhangup";
    break;
  case __mipseb_linux_idle:
    return "idle";
    break;
    /* vm86 does NOT belong in a MIPS simulator! :) */
    /*  case __mipseb_linux_vm86old:
    return "vm86old";
    break;*/
  case __mipseb_linux_wait4:
    return "wait4";
    break;
  case __mipseb_linux_swapoff:
    return "swapoff";
    break;
  case __mipseb_linux_sysinfo:
    return "sysinfo";
    break;
  case __mipseb_linux_ipc:
    return "ipc";
    break;
  case __mipseb_linux_fsync:
    return "fsync";
    break;
  case __mipseb_linux_sigreturn:
    return "sigreturn";
    break;
  case __mipseb_linux_clone:
    return "clone";
    break;
  case __mipseb_linux_setdomainname:
    return "setdomainname";
    break;
  case __mipseb_linux_uname:
    return "uname";
    break;
  case __mipseb_linux_modify_ldt:
    return "modify_ldt";
    break;
  case __mipseb_linux_adjtimex:
    return "adjtimex";
    break;
  case __mipseb_linux_mprotect:
    return "mprotect";
    break;
  case __mipseb_linux_sigprocmask:
    return "sigprocmask";
    break;
  case __mipseb_linux_create_module:
    return "create_module";
    break;
  case __mipseb_linux_init_module:
    return "init_module";
    break;
  case __mipseb_linux_delete_module:
    return "delete_module";
    break;
  case __mipseb_linux_get_kernel_syms:
    return "get_kernel_syms";
    break;
  case __mipseb_linux_quotactl:
    return "quotactl";
    break;
  case __mipseb_linux_getpgid:
    return "getpgid";
    break;
  case __mipseb_linux_fchdir:
    return "fchdir";
    break;
  case __mipseb_linux_bdflush:
    return "bdflush";
    break;
  case __mipseb_linux_sysfs:
    return "sysfs";
    break;
  case __mipseb_linux_personality:
    return "personality";
    break;
  case __mipseb_linux_afs_syscall:
    return "afs_syscall";
    break;
  case __mipseb_linux_setfsuid:
    return "setfsuid";
    break;
  case __mipseb_linux_setfsgid:
    return "setfsgid";
    break;
  case __mipseb_linux__llseek:
    return "llseek";
    break;
 case __mipseb_linux_getdents:
    return "getdents";
    break;
  case __mipseb_linux__newselect:
    return "newselect";
    break;
  case __mipseb_linux_flock:
    return "flock";
    break;
  case __mipseb_linux_msync:
    return "msync";
    break;
  case __mipseb_linux_readv:
    return "readv";
    break;
  case __mipseb_linux_writev:
    return "writev";
    break;
    // Added a few syscalls here to match the linux-threads asm-mips/unistd.h
  case __mipseb_linux_cacheflush:
    return "cacheflush";
    break;
  case __mipseb_linux_cachectl:
    return "cachectl";
    break;
  case __mipseb_linux_sysmips:
    return "sysmips";
    break;
  case __mipseb_linux_unused150:
    return "unused150";
    break;
    // End of added cases
  case __mipseb_linux_getsid:
    return "getsid";
    break;
  case __mipseb_linux_fdatasync:
    return "fdatasync";
    break;
  case __mipseb_linux__sysctl:
    return "sysctl";
    break;
  case __mipseb_linux_mlock:
    return "mlock";
    break;
  case __mipseb_linux_munlock:
    return "munlock";
    break;
  case __mipseb_linux_mlockall:
    return "mlockall";
    break;
  case __mipseb_linux_munlockall:
    return "munlockall";
    break;
  case __mipseb_linux_sched_setparam:
    return "sched_setparam";
    break;
  case __mipseb_linux_sched_getparam:
    return "sched_getparam";
    break;
  case __mipseb_linux_sched_getscheduler:
    return "sched_getscheduler";
    break;
  case __mipseb_linux_sched_yield:
    return "sched_yield";
    break;
  case __mipseb_linux_sched_get_priority_max:
    return "sched_get_priority_max";
    break;
  case __mipseb_linux_sched_get_priority_min:
    return "sched_get_priority_min";
    break;
  case __mipseb_linux_sched_rr_get_interval:
    return "sched_rr_get_interval";
    break;
  case __mipseb_linux_nanosleep:
    return "nanosleep";
    break;
  case __mipseb_linux_mremap:
    return "mremap";
    break;
    // Added cases
  case __mipseb_linux_accept:
    return "accept";
    break;
  case __mipseb_linux_bind:
    return "bind";
    break;
  case __mipseb_linux_connect:
    return "connect";
    break;
  case __mipseb_linux_getpeername:
    return "getpeername";
    break;
  case __mipseb_linux_getsockname:
    return "getsockname";
    break;
  case __mipseb_linux_getsockopt:
    return "getsockopt";
    break;
  case __mipseb_linux_listen:
    return "listen";
    break;
  case __mipseb_linux_recv:
    return "recv";
    break;
  case __mipseb_linux_recvfrom:
    return "recvfrom";
    break;
  case __mipseb_linux_recvmsg:
    return "recvmsg";
    break;
  case __mipseb_linux_send:
    return "send";
    break;
  case __mipseb_linux_sendmsg:
    return "sendmsg";
    break;
  case __mipseb_linux_sendto:
    return "sendto";
    break;
  case __mipseb_linux_setsockopt:
    return "setsockopt";
    break;
  case __mipseb_linux_shutdown:
    return "shutdown";
    break;
  case __mipseb_linux_socket:
    return "socket";
    break;
  case __mipseb_linux_socketpair:
    return "socket";
    break;
    // End of added
  case __mipseb_linux_setresuid:
    return "setresuid";
    break;
  case __mipseb_linux_getresuid:
    return "getresuid";
    break;
  case __mipseb_linux_query_module:
    return "query_module";
    break;
  case __mipseb_linux_poll:
    return "poll";
    break;
  case __mipseb_linux_nfsservctl:
    return "nfsservctl";
    break;
  case __mipseb_linux_setresgid:
    return "setresgid";
    break;
  case __mipseb_linux_getresgid:
    return "getresgid";
    break;
  case __mipseb_linux_prctl:
    return "prctl";
    break;
  case __mipseb_linux_rt_sigreturn:
    return "rt_sigreturn";
    break;
  case __mipseb_linux_rt_sigaction:
    return "rt_sigaction";
    break;
  case __mipseb_linux_rt_sigprocmask:
    return "rt_sigprocmask";
    break;
  case __mipseb_linux_rt_sigpending:
    return "rt_sigpending";
    break;
  case __mipseb_linux_rt_sigtimedwait:
    return "sigtimedwait";
    break;
  case __mipseb_linux_rt_sigqueueinfo:
    return "rt_sigqueueinfo";
    break;
  case __mipseb_linux_rt_sigsuspend:
    return "rt_sigsuspend";
    break;
    // Originally pread64 and pwrite64
  case __mipseb_linux_pread:
    return "pread";
    break;
  case __mipseb_linux_pwrite:
    return "pwrite";
    break;
  case __mipseb_linux_chown:
    return "chown";
    break;
  case __mipseb_linux_getcwd:
    return "getcwd";
    break;
  case __mipseb_linux_capget:
    return "capget";
    break;
  case __mipseb_linux_capset:
    return "capset";
    break;
  case __mipseb_linux_sigaltstack:
    return "sigaltstack";
    break;
  case __mipseb_linux_sendfile:
    return "sendfile";
    break;
  case __mipseb_linux_getpmsg:
    return "getpmsg";
    break;
  case __mipseb_linux_putpmsg:
    return "putpmsg";
    break;
  case __mipseb_linux_mmap2:
    return "mmap2";
    break;
  case __mipseb_linux_truncate64:
    return "truncate64";
    break;
  case __mipseb_linux_ftruncate64:
    return "ftruncate64";
    break;
  case __mipseb_linux_stat64:
    return "stat64";
    break;
  case __mipseb_linux_lstat64:
    return "lstat64";
    break;
  case __mipseb_linux_fstat64:
    return "fstat64";
    break;
    // Added cases
  case __mipseb_linux_pivot_root:
    return "pivot_root";
    break;
  case __mipseb_linux_mincore:
    return "mincore";
    break;
  case __mipseb_linux_madvise:
    return "madvise";
    break;
  case __mipseb_linux_getdents64:
    return "getdents64";    
    break;
  case __mipseb_linux_fcntl64:
    return "fcntl64";
    break;
    
  default:
    return "-unknown-";
    break;
  }
  return "-hmm-";
}

void PrintError (char *s, ...)
{
  va_list ap;

  fflush (stdout);
  if(!syscall_iface) {
    syscall_iface = new_SysCall();
  }
  vpi_printf ("*syscall* [pc:0x%08x] num=%d %s(): ", (int)(syscall_iface->pc), (int)GetReg (REG_V0),
	      SysCallName (GetReg(REG_V0)));

  va_start (ap, s);
  vfprintf (stdout, s, ap);
  va_end (ap);
  vpi_printf ("\n");
  fflush (stdout);
}

#define READ_FNAME(addr)					\
    i = 0;							\
    do {							\
      c = ReadByte (addr+i);					\
      buf[i] = c;						\
      i++;							\
      if (i == 1023) {						\
	PrintError ("input filename exceeds 1023 chars!");	\
	buf[1023] = 0;						\
	break;							\
      }								\
    } while (c != 0);


void EmulateSysCall (SysCall *sc)
{
  static unsigned char buf[1024];
  long long i;
  unsigned char c;
  extern int errno;
  int x;
  //int y;
  static int depth = 0;
  //LL curaddr;
  
  //vpi_printf("\n\nEmulating syscall %d...\n", GetReg(REG_V0));

  sc->quit = 0;
  /*  
      vpi_printf("v0: %d, a0: %x, a1: %x, a2: %x, a3: %x\n",
      (int)GetReg(REG_V0), (long)GetReg(REG_A0), (long)GetReg(REG_A1),
      (long)GetReg(REG_A2), (long)GetReg(REG_A3));
  */
  switch ((int) GetReg (REG_V0)) {
   
  case __mipseb_linux_exit:             // exit (a0)
    vpi_printf ("\nEXIT called, code: %d\n", GetReg(REG_A0));
    sc->quit = 1;
    break;
  case __mipseb_linux_uname:
    //vpi_printf("__mipseb_linux_uname\n");
    UNIX_RETURN(0);
    break;
   
  case __mipseb_linux_write:		// write (fd, addr, len)
    //    vpi_printf("__mipseb_linux_write\n");
    //    vpi_printf("fd: %d\n",GetReg(REG_A0));
    //    vpi_printf("buff pointer: 0x%08x\n",GetReg(REG_A1));
    //    vpi_printf("count: %d\n",GetReg(REG_A2));
    if(1)
      {
	int destfd = sc->_fdlist[0xff & GetReg(REG_A0)];
	if (destfd < 0) {
	  PrintError ("invalid fd (app=%d, real=%d)", 
		      (int)GetReg(REG_A0),
		      destfd);
	  UNIX_RETURN (MINUS_ONE);
	}
	//vpi_printf("write output: ");
	for (i=0; i < GetReg(REG_A2); i++) {
	  c = (  ReadByte (GetReg(REG_A1)+i));
	  if (destfd == 1 || destfd == 2) {
	    vpi_printf("%c", c); // redirect stdout, stderr to VPI console.
	    x = 1;
	  } else
	    x = write (destfd,&c, 1);
	  //	  vpi_printf("buf[%d]='%c'\n", i, c);
	  
	  //vpi_printf("i = %i\tc(hex) = 0x%02x\tc = %i\tx = %i\tword = 0x%08x\n",i,c,c,x,ReadWord(GetReg(REG_A1)+i));
	  //vpi_printf("i = %i\tc = %i\tx = %i\n",i,c,x);
	  if (x != 1) {
	    if (x == 0)
	      {
		UNIX_RETURN (i+1);
	      }
	    UNIX_RETURN (MINUS_ONE);
	  }
	}
	//vpi_printf("\n\n");
	UNIX_RETURN (GetReg(REG_A2));
	break; 
      }
    
  case __mipseb_linux_read:		// read (fd, addr, len)
    //vpi_printf("__mipseb_linux_read\n");
#ifdef USE_STANDARD
    if( (0xff & GetReg (REG_A0)) < 3) 
#else
      if(1)
#endif
	{ 
	  unsigned char * buffer_temp; 
	  if (sc->_fdlist[0xff & GetReg (REG_A0)] < 0) {
	    PrintError ("invalid fd (app=%d, real=%d)", 
			(int)GetReg(REG_A0),
			sc->_fdlist[0xff & GetReg (REG_A0)]);
	    UNIX_RETURN (MINUS_ONE);
	  }
	  
	  if (GetReg(REG_A2) > 0) {
	    if (sc->_fdlist[0xff & GetReg (REG_A0)] == 0) {
	      
	x = read (sc->_fdlist[0xff & GetReg(REG_A0)], &c, 1);
	if (x == 1) {
	  WriteByte (GetReg(REG_A1), c);
	  UNIX_RETURN (1ULL);
	}
	else {
	  UNIX_RETURN (x);
	}
	break;
	    }
	    else {
	      if (GetReg (REG_A2) > 1024) {
		buffer_temp = (unsigned char * )malloc(GetReg (REG_A2));
		// x = read (_fdlist[0xff & GetReg(REG_A0)], buf, 1024);
		x = read (sc->_fdlist[0xff & GetReg(REG_A0)], buffer_temp,GetReg (REG_A2));
	      }
	      else {
		x = read (sc->_fdlist[0xff & GetReg(REG_A0)], buf, (int)GetReg (REG_A2));
	}
	      if (x < 0) {
		UNIX_RETURN (x);
		break;
	      }
        
	      if(x > 1024)
		{
		  for (i=0; i < x; i++)
		    WriteByte (GetReg (REG_A1)+i, buffer_temp[i]);
		  free(buffer_temp);
		}
	      else
		for (i=0; i < x; i++)
		  WriteByte (GetReg (REG_A1)+i, buf[i]);  
	      
	      UNIX_RETURN (x);
	      break;
	    }
	  }
	  UNIX_RETURN (0);
	  break;
	}
    

    
  case __mipseb_linux_open:		// open (file, type)
    READ_FNAME (GetReg(REG_A0));
    {
      //vpi_printf("__mipseb_linux_open\n");
      
      for (i=0; i < 256; i++)
	if (sc->_fdlist[i] == -1)
	  break;
      if (i == 256)
	UNIX_RETURN(MINUS_ONE);
      sc->_fdlist[i] = open (buf, mode_remap (GetReg(REG_A1)), GetReg(REG_A2));
      if (sc->_fdlist[i] < 0) {
	PrintError ("error opening file `%s'", buf);
	UNIX_RETURN (MINUS_ONE);
      }
      else {
	UNIX_RETURN(i);
      }
    }
    break;
  case __mipseb_linux_close:		// close (fd)
    {
      //vpi_printf("__mipseb_linux_close\n");
      int tmpfd = sc->_fdlist[0xff & GetReg(REG_A0)];
      sc->_fdlist[0xff & GetReg(REG_A0)] = -1;
      UNIX_RETURN (close (tmpfd));
      break; 
    }
    
  case __mipseb_linux_fstat64: // Blindly copying fxstat code
    {
      //vpi_printf("__mipseb_linux_fxstat64\n");
      int blah = 0;
      blah = _emulate_fxstat (sc->_fdlist[0xff & GetReg(REG_A1)], GetReg(REG_A2));
      //printf("blah is now assigned and is %d\n",blah);
      if (blah == -1) {
	//printf("calling unix_return(minus_one)\n");
	UNIX_RETURN(MINUS_ONE);
      } 
      else {
	UNIX_RETURN (blah);
      }
      //printf("finished fstat UNIX_RETURN\n");
      break;
    }
  case __mipseb_linux_mmap: // Writing from scratch
    //vpi_printf("__mipseb_linux_mmap\n");
    // mmap function declaration
    // void *mmap(void *addr, size_t len, int prot, int flags, int fildes, off_t off); 
    // There are a number of flags for prot that need to be checked
    /*
    LL addr = GetReg(REG_A0);
    LL len  = GetReg(REG_A1);
    LL prot = GetReg(REG_A2);
    LL flags= GetReg(REG_A3);
    LL fildes,off;
    LL SP = GetReg(REG_SP);
    */
    // Ignored flags: MAP_DENYWRITE/MAP_ANON, MAP_FILE, MAP_EXECUTABLE
    
    // MAP_SHARED & MAP_PRIVATE flags are mutually exclusive, and 1 must be set.
    

    // glibc recognizes that mmap failed but still completes execution.
    // Return value if mmap failed
    UNIX_RETURN(-1);
    break;


  case __mipseb_linux_creat:		// creat (file, int)
    //vpi_printf("__mipseb_linux_creat\n");
    READ_FNAME(GetReg(REG_A0));
    for (i=0; i < 256; i++) 
      if (sc->_fdlist[i] == -1)
	break;
    if (i == 256)
      UNIX_RETURN (MINUS_ONE);
    sc->_fdlist[i] = creat (buf, GetReg(REG_A1));
#if 0
    vpi_printf("syscall: fd is %d\n",i);
#endif
    UNIX_RETURN (i);
    break;
  case __mipseb_linux_syscall:
    //vpi_printf("__mipseb_linux_syscall\n");
    // unbelivably, this is a syscall!
    if (depth)
      fatal_error ("Recursive call to __mipseb_linux_syscall???");
    {
      LL a0, a1, a2, a3;
      a0 = GetReg (REG_A0);
      a1 = GetReg (REG_A1);
      a2 = GetReg (REG_A2);
      a3 = GetReg (REG_A3);
      SetReg (REG_V0, a0);
      SetReg (REG_A0, a1);
      SetReg (REG_A1, a2);
      SetReg (REG_A2, a3);
      // wow!
      depth++;
      EmulateSysCall (sc);
      depth--;
      SetReg (REG_A0, a0);
      SetReg (REG_A1, a1);
      SetReg (REG_A2, a2);
      return;
    }      
    break;
  
  case __mipseb_linux_brk:			// brk()
    vpi_printf("SYS_brk\n");
    // since we have no memory management, just return ok! :)
    SetReg (REG_V0,0);
    printf ("request for %x bytes\n", (unsigned long)GetReg (REG_A0));
    UNIX_RETURN (0);
    break;

  case __mipseb_linux_fstat:		// fstat with a twist...
    {
      //vpi_printf("__mipseb_linux_fxstat64\n");
      int blah = 0;
      blah = _emulate_fxstat (sc->_fdlist[0xff & GetReg(REG_A1)], GetReg(REG_A2));
      //printf("blah is now assigned and is %d\n",blah);
      if (blah == -1) {
	//printf("calling unix_return(minus_one)\n");
	UNIX_RETURN(MINUS_ONE);
      } 
      else {
	UNIX_RETURN (blah);
      }
      //printf("finished fstat UNIX_RETURN\n");
      break;
    }

  case __mipseb_linux_lseek:
    vpi_printf("SYS_lseek\n");
    if (sc->_fdlist[0xff & GetReg (REG_A0)] < 0) {
      PrintError ("invalid fd (app=%d, real=%d)", 
		  (int)GetReg(REG_A0),
		  sc->_fdlist[0xff & GetReg (REG_A0)]);
      UNIX_RETURN (MINUS_ONE);
    }
    else {
      UNIX_RETURN (lseek (sc->_fdlist[0xff & GetReg (REG_A0)],
			  GetReg (REG_A1),
			  GetReg (REG_A2)));
    }
    break;

  case __mipseb_linux_getpid:
    UNIX_RETURN (getpid());
    break;

  case __mipseb_linux_getuid:
    UNIX_RETURN (getuid());
    break;

  case __mipseb_linux_time:
    {
      time_t x, y;

      x = time (&y);
      printf("Got time: %d\n", y);
      if (GetReg (REG_A0) != 0) {
        vpi_printf ("Due to a stale cache data issue, please always use \"tim=time(NULL)\" format\n");
        exit(1);
        //WriteWord (GetReg (REG_A0), (int)y);
      }
      UNIX_RETURN (x);
    }
    break;

  // written from scratch
  case __mipseb_linux_socket:
    UNIX_RETURN (socket (GetReg(REG_A0), GetReg(REG_A1), GetReg(REG_A2)));
    break;

  case __mipseb_linux_connect:
    UNIX_RETURN (connect (GetReg(REG_A0), GetReg(REG_A1), GetReg(REG_A2)));
    break;
    
  default:
    PrintError ("Unimplemented system call");
    UNIX_RETURN (0);
    break;
  }
    /*
      case SYS_ioctl:		// ioctl (fd, request, ...)
      vpi_printf("SYS_ioctl\n");
      // XXX: fixme. This needs to translate the ioctl from 
      // irix5.3 to local host
      //vpi_printf ("pc: %x, ioctl, r4=%x, r5=%x, r6=%x\n",
      //pc,
      //GetReg (REG_A0), GetReg(REG_A1), GetReg(REG_A2));
      if (sc->_fdlist[0xff & GetReg(REG_A0)] < 0) {
      PrintError ("invalid fd (app=%d, real=%d)", 
      (int)GetReg(REG_A0),
      sc->_fdlist[0xff & GetReg (REG_A0)],GetReg(REG_A1));
      UNIX_RETURN (MINUS_ONE);
      }
      switch (GetReg (REG_A1)) {
      #ifdef TCGETA
      case SIM_TCGETA:
      vpi_printf("TCGETA defined\n");
      // Must do native linux call here.
      UNIX_RETURN(ioctl(sc->_fdlist[0xff &GetReg(REG_A0)],GetReg(REG_A1),GetReg(REG_A2)));
      break;
      #else
      case SIM_TCGETA:
      vpi_printf("TCGETA undefined\n");
      break;
      #endif
      default:
      PrintError ("fd (app=%d, real=%d), cmd=%d (%x)",
      (int)GetReg(REG_A0),
      sc->_fdlist[0xff & GetReg (REG_A0)],
      (int)GetReg (REG_A1), (int)GetReg (REG_A1));
      break;
      }
      UNIX_RETURN (0);
      break;
    */
    /*

  case SYS_xstat:
    READ_FNAME(GetReg(REG_A1));
    {
      vpi_printf("SYS_xstat\n");
      int fd;

      fd = open (buf, O_RDONLY);
      if (fd < 0) {
	PrintError ("error opening file `%s'", buf);
	UNIX_RETURN (MINUS_ONE);
      }
      else {
	i = _emulate_fxstat (fd, GetReg(REG_A2));
	close (fd);
	UNIX_RETURN(i);
      }
    }
    break;
    
  case SYS_access:
    vpi_printf("SYS_access\n");
    READ_FNAME (GetReg (REG_A0));
    UNIX_RETURN(access (buf, GetReg(REG_A1)));
    break;
    
  case SYS_fxstat:		// fstat with a twist...
    vpi_printf("SYS_fxstat\n");
    UNIX_RETURN (_emulate_fxstat (sc->_fdlist[0xff & GetReg(REG_A1)], GetReg(REG_A2)));
    break;

  case SYS_prctl:		// prctl
    vpi_printf("SYS_prctl\n");
    if (GetReg(REG_A0) == 14) {
      UNIX_RETURN (0);
    }
    else {
      PrintError ("code %d unimplemented", (int)GetReg (REG_A0));
    }
    break;
    
  case SYS_brk:			// brk()
    vpi_printf("SYS_brk\n");
    // since we have no memory management, just return ok! :)
    //SetReg (REG_V0,0);
    //printf ("request for %x bytes\n", (unsigned long)GetReg (REG_A0));
    UNIX_RETURN (0);
    break;
    
  case SYS_BSD_getime:
    vpi_printf("SYS_getime\n");
    UNIX_RETURN (_emulate_gettime (GetReg(REG_A0), GetReg(REG_A1)));
    break;
    

    
  case SYS_sysmp: // sysmp (int cmd, ...)
    vpi_printf("SYS_sysmp\n");
    switch (GetReg (REG_A0)) {
    case SIM_MP_PGSIZE:
      UNIX_RETURN (4096);
      break;
      
    default:
      PrintError ("unimpl cmd=%d", (int)GetReg (REG_A0));
      UNIX_RETURN (MINUS_ONE);
      break;
    }
    
  case SYS_ksigaction:
    vpi_printf("SYS_ksgiaction\n");
    // no one knows what this does...
    PrintError ("unimpl");
    UNIX_RETURN (0);
    break;
    
  case SYS_lseek:
    vpi_printf("SYS_lseek\n");
    if (sc->_fdlist[0xff & GetReg (REG_A0)] < 0) {
      PrintError ("invalid fd (app=%d, real=%d)", 
		  (int)GetReg(REG_A0),
		  sc->_fdlist[0xff & GetReg (REG_A0)]);
      UNIX_RETURN (MINUS_ONE);
    }
    else {
      UNIX_RETURN (lseek (sc->_fdlist[0xff & GetReg (REG_A0)],
			  GetReg (REG_A1),
			  GetReg (REG_A2)));
    }
    break;
    
  case SYS_time:
    {
      vpi_printf("SYS_time\n");
      time_t x, y;
      
      x = time (&y);
      
      if (GetReg (REG_A0) != 0) {
	WriteWord (GetReg (REG_A0), (int)y);
      }
      UNIX_RETURN (x);
    }
    break;

  case SYS_syssgi:
    vpi_printf("SYS_syssgi\n");
    switch (GetReg (REG_A0)) {
      
    default:
      PrintError ("unimpl, cmd=%d", (int)GetReg (REG_A0));
      break;
    }
    break;
    
  case SYS_getpid:
    vpi_printf("SYS_getpid\n");
    UNIX_RETURN (getpid());
    break;
    
  case SYS_kill:
    vpi_printf("SYS_kill\n");
    UNIX_RETURN (kill ((int)GetReg (REG_A0), (int)GetReg(REG_A1)));
    break;
    
    
  case SYS_backdoor:
    
     // simulator backdoor calls go here...
    
    vpi_printf("SYS_backdoor\n");
    switch (GetReg (REG_A0)) {
    case BackDoor_SetArgs:
      if ((sc->_argc > 0) && (GetCpuId()==0)) {
	// we have space to store args starting at _argaddr 
	
	// 1. adjust $sp, keeping it double-word aligned 
	SetReg (REG_SP, GetReg (REG_SP) - 4*(sc->_argc + 1 + !(sc->_argc & 1)));
	
	// write argc 
	WriteWord (GetReg (REG_SP), sc->_argc);
	
	// write argv 
	curaddr = sc->_argaddr;
	for (i=0; i < sc->_argc; i++) {
	  WriteWord (GetReg (REG_SP) + (4+4*i), curaddr);
	  y = strlen (sc->_argv[i]);
	  for (x=0; x <= y; x++) {
	    WriteByte (curaddr, sc->_argv[i][x]);
	    curaddr++;
	  }
	}
      }
      UNIX_RETURN (0);
      break;
    case BackDoor_Delay :
      PAUSE(GetReg(REG_A1)*2000);  //us
      UNIX_RETURN (0);
      break;
    case BackDoor_SimTime:
      // return time in register $a0 
      SetReg (REG_A0, GetTime());
      UNIX_RETURN (0);
      break;
    case BackDoor_CpuId:
      SetReg (REG_A0, GetCpuId());
      UNIX_RETURN (0);
      break;
    case BackDoor_ResetStats: 
      ResetCall();
      UNIX_RETURN (0);
      break;
    case BackDoor_PlaceRange:
      PlaceRangeCall((unsigned)GetReg(REG_A1),(unsigned)GetReg(REG_A2),
		     (unsigned)GetReg(REG_A3));
      UNIX_RETURN (0);
      break;
    case BackDoor_ActiveProcs:
      UNIX_RETURN (0);
      break;
    case BackDoor_IOMap:
      UNIX_RETURN (0);
      break;
    case BackDoor_Create:
      CreateCall((unsigned)GetReg(REG_A1),(unsigned)GetReg(REG_A2));
      UNIX_RETURN (0);
      break;
    case BackDoor_IOMapGeneral:
      UNIX_RETURN (0);
      break;
    case BackDoor_MemoryMap:
      UNIX_RETURN (0);
      break;
    case BackDoor_GetPhysAddr:
      UNIX_RETURN (0);
      break;
    case BackDoor_GetNodeNum:
      UNIX_RETURN (0);
      break;
    case BackDoor_HitWBInvalD:
      UNIX_RETURN (0);
      break;
    case BackDoor_HitWBInvalS:
      UNIX_RETURN (0);
      break;
    case BackDoor_IndexWBInvalD:
      UNIX_RETURN (0);
      break;
    case BackDoor_IndexWBInvalS:
      UNIX_RETURN (0);
      break;
    case BackDoor_FlushD:
       UNIX_RETURN (0);
       break;
    case BackDoor_FlushS:
       UNIX_RETURN (0);
       break;
    case BackDoor_PageFlushD:
       UNIX_RETURN (0);
       break;
    case BackDoor_PageFlushS:
       UNIX_RETURN (0);
       break;
    case BackDoor_WaitForEnd:
      WaitCall((unsigned)GetReg(REG_A1));
      UNIX_RETURN (0);
      break;
    default:
      PrintError ("Unknown backdoor call %d\n", (int)GetReg(REG_A0));
      break;
    }
    UNIX_RETURN (0);
    break;
    */
  //printf("emulate syscall done\n");
}


/*************************************************************************
 *
 *
 *  Translate mips-linux (formerly mips-sgi-irix) structures to/from host 
 *  structures
 *
 *
 *************************************************************************
 */

/* mode types for open() */

static unsigned int mode_remap (unsigned int x)
{
  unsigned int res = 0;

#define FIXUP(v)   do  { if (x & SIM_O_##v) res = res |O_##v; x &= ~SIM_O_##v; } while (0)
#define DONT_HAVE(v) if (x & SIM_O_##v) {vpi_printf ("skipping flag: " #v); }
  
  FIXUP(RDONLY);
  FIXUP(WRONLY);
  FIXUP(RDWR);
  FIXUP(NDELAY);
  FIXUP(APPEND);
  DONT_HAVE(SYNC);
  FIXUP(NONBLOCK);
  DONT_HAVE(DIRECT);
  FIXUP(CREAT);
  FIXUP(TRUNC);
#undef FIXUP
#undef DONT_HAVE

  if (x != 0) {
   vpi_printf ("mode_remap: could not properly emulate all flags...\n");
  }
  return res;
}

LL _emulate_gettime(LL ts_addr, LL tz_addr)
{
  struct timeval tv;
  mips_timestruc_t mtv;

  int x, i;

  i = gettimeofday (&tv, 0);

#define WORD_COPY(field,lfield)  do {                                        \
			    x = (intptr_t)&mtv.field - (intptr_t)&mtv;               \
			    Assert (sizeof (mtv.field) == sizeof(tv.lfield), \
			            "Oh my god. You're dead");               \
			    Assert (sizeof (mtv.field) == 4,                 \
			            "Oh my god. You're dead -- wc2");               \
			    WriteWord (ts_addr+x, tv.lfield);              \
			  } while (0)

  WORD_COPY (tv_sec,tv_sec);
  WORD_COPY (tv_nsec,tv_sec);
#undef WORD_COPY
  return i;
}


/*
 *
 *  fstat call
 *
 */



LL _emulate_fxstat (int fd, LL addr)
{
  struct stat sb;
  // Now that we're compiling for mips-linux, the structs should be identical. Right?
  //struct mips_stat msb;
  struct stat msb;
  int x, i;
  i = fstat (fd, &sb);
#if 0
  //vpi_printf("kkk\n");
 vpi_printf("dev_t is %d\n",sizeof(dev_t));
 vpi_printf("ino_t is %d\n",sizeof(ino_t));
 vpi_printf("mode_t  is %d\n",sizeof(mode_t));
 vpi_printf("sb mode_t  is %d\n",sizeof(sb.st_mode));
 vpi_printf("msb mode_t  is %d\n",sizeof(msb.st_mode));
 vpi_printf("nlink_t  is %d\n",sizeof(nlink_t));
 vpi_printf("sb.st_size is %d\n",sizeof(sb.st_size));
 vpi_printf("msb.st_size is %d\n",sizeof(msb.st_size));
 vpi_printf("sb.st_blocks is %d\n",sizeof(sb.st_blocks));
 vpi_printf("msb.st_blocks is %d\n",sizeof(msb.st_blocks));
 vpi_printf("sb.st_blksize is %d\n",sizeof(sb.st_blksize));
 vpi_printf("msb.st_blksize is %d\n",sizeof(msb.st_blksize));
 vpi_printf("uid_t is %d\n",sizeof(uid_t));
 vpi_printf("gid_t is %d\n",sizeof(gid_t));
 vpi_printf("off_t is %d\n",sizeof(off_t));
#endif
#if 0 
 vpi_printf("fstat debugging:\n");
 vpi_printf("sb.st_dev: %i\n",0xff & sb.st_dev);
 vpi_printf("sb.st_ino: %i\n",0xf & sb.st_ino);
 vpi_printf("sb.st_mode: %i\n",0xf & sb.st_mode);
 vpi_printf("sb.st_nlink: %i\n",0xf & sb.st_nlink);
 vpi_printf("sb.st_uid: %i\n",0xf & sb.st_uid);
 vpi_printf("sb.st_gid: %i\n",0xf & sb.st_gid);
 vpi_printf("sb.st_rdev: %i\n",0xff & sb.st_rdev);
 vpi_printf("sb.st_size: %i\n",0xf & sb.st_size);
 vpi_printf("sb.st_blksize: %i\n",0xf & sb.st_blksize);
 vpi_printf("sb.st_blocks: %i\n",0xf & sb.st_blocks);
 vpi_printf("sb.st_atime: %i\n",0xf & sb.st_atime);
 vpi_printf("sb.st_mtime: %i\n",0xf & sb.st_mtime);
 vpi_printf("sb.st_ctime: %i\n",0xf & sb.st_ctime);
#endif

#define WORD_COPY(field,lfield)  do {                                        \
    x = (intptr_t)&msb.field - (intptr_t)&msb;					\
    Assert (sizeof (msb.field) == sizeof(sb.lfield),			\
	    "Oh my god. You're dead");					\
    Assert (sizeof (msb.field) == 4,					\
	    "Oh my god. You're dead -- wc1");					\
    WriteWord (addr+x, sb.lfield);					\
  } while (0)
  
#define HALF_COPY(field,lfield)  do {					\
    x = (intptr_t)&msb.field - (intptr_t)&msb;					\
    Assert (sizeof (msb.field) == sizeof(sb.lfield),			\
	    "Oh my god. You're dead");					\
    Assert (sizeof (msb.field) == 2,					\
	    "Oh my god. You're dead");					\
    WriteHalf (addr+x, sb.lfield);					\
  } while (0)
  
#define H_TO_WORD_COPY(field,lfield)  do {				\
    x = (intptr_t)&msb.field - (intptr_t)&msb;					\
    Assert (sizeof (msb.field) == 2*sizeof(sb.lfield),			\
	    "Oh my god. You're dead");					\
    Assert (sizeof (msb.field) == 4,					\
	    "Oh my god. You're dead");					\
    WriteWord(addr+x, sb.lfield);					\
  } while (0)
  
 // Added to support 8 byte field sizes for dev_t
#define DBL_WORD_COPY(field,lfield)  do {				\
    x = (intptr_t)&msb.field - (intptr_t)&msb;					\
    Assert (sizeof (msb.field)== sizeof(sb.lfield),			\
	    "Oh my god. You're dead");					\
    Assert (sizeof (msb.field) == 8,					\
	    "Oh my god. You're dead");					\
    WriteWord (addr+x, (int)sb.lfield);				\
    WriteWord (addr+x+x,sb.lfield >> 32);				\
  } while (0)
 /*
   #define D_TO_WORD_COPY(field,lfield)  do {				\
   x = (intptr_t)&msb.field - (intptr_t)&msb;					\
   Assert (2*sizeof (msb.field)== sizeof(sb.lfield),			\
   "Oh my god. You're dead");						\
   Assert (sizeof (msb.field) == 4,					\
   "Oh my god. You're dead");						\
   WriteWord (addr+x, (int)sb.lfield);					\
   } while (0)
 */

  DBL_WORD_COPY (st_dev,st_dev);
  DBL_WORD_COPY (st_ino,st_ino);
  WORD_COPY (st_mode,st_mode);
  DBL_WORD_COPY (st_nlink,st_nlink);
  WORD_COPY (st_uid,st_uid);
  WORD_COPY (st_gid,st_gid);
  DBL_WORD_COPY (st_rdev,st_rdev);
  DBL_WORD_COPY (st_size,st_size);
  DBL_WORD_COPY (st_blocks,st_blocks);
  DBL_WORD_COPY (st_blksize,st_blksize);




 
 /*
   WORD_COPY (st_dev,st_dev);
   WORD_COPY (st_ino,st_ino);
   H_TO_WORD_COPY (st_mode,st_mode);
   H_TO_WORD_COPY (st_nlink,st_nlink);
   WORD_COPY (st_uid,st_uid);
   WORD_COPY (st_gid,st_gid);
   WORD_COPY (st_rdev,st_rdev);
   D_TO_WORD_COPY (st_size,st_size);
   D_TO_WORD_COPY (st_blocks,st_blocks);
   WORD_COPY (st_blksize,st_blksize);
 */


#if 0
 vpi_printf("st_size offset is %d\n",(int)&msb.st_size - (int)&msb);
 vpi_printf("file size is %d\n",sb.st_size);
#endif


#if defined(__i386__) && defined (__FreeBSD__)
  WORD_COPY (st_atimespec.tv_sec,st_atimespec.tv_sec);
  WORD_COPY (st_atimespec.tv_nsec,st_atimespec.tv_sec);
#else
#if 0
#error Need to fix fxstat emulation
#endif
#endif
    
#undef WORD_COPY
#undef HALF_COPY
#undef DBL_WORD_COPY
  //printf("completed fstat emulation -- i = %d\n",i);
  return i;
  }


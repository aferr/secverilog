#
#  $Id: Makefile,v 1.3 1999/08/21 04:01:32 rajit Exp $
#
#
#

RM = /bin/rm 
CCMKDEP=gcc
#
# standard defines
#
IMAGES=hello host sample problem loadh loadhu storeh towers nqueen fib bigfib msort vadd multdiv search

TARGETS= $(IMAGES) $(addsuffix .inf,$(IMAGES))
GENFILES=$(addsuffix .ld,$(IMAGES))

all: $(TARGETS)

CC=$(MIPS_HOME)/host-cc.pl -k
CFLAGS=

#%: %.s
#	$(CC) -r $*.s -o $* -k
clean: 
	rm -f *.o *.ld $(TARGETS)
clobber:
	rm -rf *.o *.ld *~ $(TARGETS) ../*verilog.log ../*verilog.key ../INCA_libs ../waves.shm
 

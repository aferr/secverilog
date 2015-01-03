# This is a makefile for gcc compatible make.
# May require alterations for some make programs.
# HP-UX make may require file to be altered.

# extension for object files
O = o

# commands
CC = $(MIPS_HOME)/host-cc.pl -k
#CC = gcc
CPP = cpp
LIB = ar
ASM = as
RANLIB = ranlib

# name of temporary library script
TEMPFILE = $(TEMP)/temp.mak

# standard include directory
STDINCDIR=include

# The places to look for include files (in order).
INCL =  -I . -I $(RSAEURODIR) -I $(STDINCDIR)

# Extra Defs

# To select CPU type set CPUT to any of the following
#
# 386 = i386+ processor, 80386 and above processor
# 68k = M680x0 series processor.
#
# Leave empty to disable assembler routines.
CPUT =

# Set to 1 for ANSI Standard Routine to be Used, only availible
# if assembler routines not it use.
ANSISTD = 

# utility routines
del = rm -f
COPY = cp -f

# name of main executable to build
PROG = all

# Normal C flags.
ifdef CPUT
CFLAGS = $(INCL) -c -DPROTOTYPES=0 -DUSEASM=1 -DDES386=1
else
ifdef ANSISTD
CFLAGS = $(INCL) -c -DPROTOTYPES=0 -DUSA_ANSI=1
else
CFLAGS = $(INCL) -c -DPROTOTYPES=0 
endif
endif

ASMFL = $(INCL) -c -Wa,-L
MFLAGS = -I. -I$(RSAEURODIR)

# The location of the common source directory.
RSAEURODIR = ../source/
RSAEUROLIB = rsaeuro.a
RSAREFLIB = rsaref.a

# The location of the demo source directory.
RDEMODIR = ../rdemo/
DEMODIR = ../demo/

ifdef CPUT
all : rstdasm.$(O) demo $(RSAREFLIB)

# Use ASMCODE for some key routines
rstdasm.$(O) : $(RSAEURODIR)rsa$(CPUT).s
	$(CC) $(ASMFL) $(RSAEURODIR)rsa$(CPUT).s -o rstdasm.$(O)

desasm.$(O) : $(RSAEURODIR)des$(CPUT).s
	$(CPP) $(RSAEURODIR)des$(CPUT).s | $(ASM) -o desasm.$(O)
else
all : demo $(RSAREFLIB)

# Make sure we use the C version of the routines
clean :
	$(del) *.$(O)
	$(del) $(RSAREFLIB)
	$(del) randemo mdemo redemo rsademo
	$(del) randemo.inf mdemo.inf redemo.inf rsademo.inf
	$(del) randemo.ld mdemo.ld redemo.ld rsademo.ld
endif

$(RSAREFLIB) : $(RSAEUROLIB) mitigate.h
	$(COPY) $(RSAEUROLIB) $(RSAREFLIB)

demo : redemo mdemo randemo rsademo

randemo : randemo.$(O) $(RSAEUROLIB)
	$(CC) -o $@ randemo.$(O) $(RSAEUROLIB)

mdemo : mdemo.$(O) $(RSAEUROLIB)
	$(CC) -o $@ mdemo.$(O) $(RSAEUROLIB)

redemo : redemo.$(O) $(RSAEUROLIB)
	$(CC) -o $@ redemo.$(O) $(RSAEUROLIB)

rsademo : rsademo.$(O) $(RSAEUROLIB)
	$(CC) -o $@ rsademo.$(O) $(RSAEUROLIB)

ifdef CPUT
$(RSAEUROLIB) : desc.$(O) shsc.$(O) md2c.$(O) md4c.$(O) md5c.$(O) nn.$(O) prime.$(O)\
	rsa.$(O) r_encode.$(O) r_dh.$(O) r_enhanc.$(O) r_keygen.$(O) r_random.$(O)\
	r_stdlib.$(O) rstdasm.$(O) desasm.$(O)
	$(LIB) r $@ $?
	$(RANLIB) $@
else
$(RSAEUROLIB) : desc.$(O) shsc.$(O) md2c.$(O) md4c.$(O) md5c.$(O) nn.$(O) prime.$(O)\
	rsa.$(O) r_encode.$(O) r_dh.$(O) r_enhanc.$(O) r_keygen.$(O) r_random.$(O)\
	r_stdlib.$(O)
	$(LIB) r $@ $?
	$(RANLIB) $@
endif

randemo.$(O) : $(DEMODIR)randemo.c $(RSAEURODIR)global.h $(RSAEURODIR)rsaref.h
	$(CC) $(CFLAGS) -o $(RSAEURODIR)randemo.$(O) $(DEMODIR)randemo.c

mdemo.$(O) : $(DEMODIR)mdemo.c $(RSAEURODIR)global.h $(RSAEURODIR)rsaref.h
	$(CC) $(CFLAGS) -o $(RSAEURODIR)mdemo.$(O) $(DEMODIR)mdemo.c

redemo.$(O) : $(DEMODIR)redemo.c $(RSAEURODIR)global.h $(RSAEURODIR)rsaref.h
	$(CC) $(CFLAGS) -o $(RSAEURODIR)redemo.$(O) $(DEMODIR)redemo.c

rsademo.$(O) : $(DEMODIR)rsademo.c $(RSAEURODIR)global.h $(RSAEURODIR)rsaref.h $(RSAEURODIR)mitigateutil.h
	$(CC) $(CFLAGS) -o $(RSAEURODIR)rsademo.$(O) $(DEMODIR)rsademo.c

include $(RSAEURODIR)targets.mak

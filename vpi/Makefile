CFLAGS := -fPIC -g -I/opt/cadence/ius/tools/verilog/include/ -Wall
#CFLAGS := -fPIC -g -I/opt/cadence/ldv/tools/verilog/include -Wall
SOURCES := vpi_user.c
SOURCES += cachecore.c
SOURCES += dis.c
SOURCES += mem.c
SOURCES += misc.c
SOURCES += mydis.c
SOURCES += mips.c
SOURCES += sys.c
SOURCES += syscall.c
SOURCES += vcache.c
SOURCES += controls.c
OBJECTS := $(SOURCES:.c=.o)
               
libvpi.so: $(OBJECTS)
	ld -shared /usr/lib64/libc.a $(OBJECTS) /usr/lib64/libc_nonshared.a -o libvpi.so

install: libvpi.so
	/usr/bin/install -g ece314 -m 664 -p libvpi.so /classes/ece314/lib
clean:
	rm -f $(OBJECTS) libvpi.so

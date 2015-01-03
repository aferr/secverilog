#!/bin/sh

# configure openssl for our MIPS processor
setarch i386 ./config --prefix="$PWD" --openssldir="$PWD/openssl" no-threads no-asm

# edit the generated MAKEFILE to remove O3 option, and set the machine to be big endian
sed -i '/^CFLAG/s/-O3//' Makefile # remove -O3 option
sed -i '/^CFLAG/s/-DL_ENDIAN/-DB_ENDIAN/' Makefile

# replace the gcc tools with mipseb-linux-***
sed -i '/^CC/s/gcc/${MIPS_HOME}\/host-cc.pl -k/' Makefile
sed -i '/^AR/s/ar/mipseb-linux-ar/' Makefile
sed -i '/^NM/s/nm/mipseb-linux-nm/' Makefile
sed -i '/^RANLIB/s/\/usr\/bin\/ranlib/mipseb-linux-ranlib/' Makefile
sed -i '/^MAKEDEPPROG/s/gcc/${MIPS_HOME}\/host-cc.pl -k/' Makefile

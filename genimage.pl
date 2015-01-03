#!/usr/bin/perl
#
# WARNING WARNING WARNING: This is a *HUGE* hack!
#
# $Id: genimage.pl,v 1.2 1999/04/05 14:05:39 rajit Exp $
#


die "Usage: $0 <mips-exe-file>" unless $#ARGV >= 0;
die "File $ARGV[0] doesn't exist!" unless -f $ARGV[0];

$tmpfile = $ARGV[0];
$ldfile = "$tmpfile";
$infFile = "$tmpfile.inf";

if ($#ARGV > 0) {
  shift;
  @list = @ARGV;
}
else {
  @list = (
	   ".note.ABI-tag",
	   ".reginfo",
	   ".init",
	   ".text",
	   "__libc_freeres_fn",
	   ".fini",
	   ".rodata",
	   ".eh_frame",
	   ".ctors",
	   ".dtors",
	   ".jcr",
	   ".data",
	   ".sbss",
	   ".bss",
	   "__libc_freeres_ptrs"
	  );
}

foreach $i (@list) {

  open(OBJ,"mipseb-linux-objdump -j $i --full-contents $ldfile|");
  $found = 0;
  while (<OBJ>) {
    if (/^Contents of section $i/) {
      $found = 1;
      last;
    }
  }

  next if $found == 0;

  while (<OBJ>) {
    /\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)/ || /\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)/ || /\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)/;
    printf ("0x00000000%08x 0x%08x%08x\n", hex($1),hex($2),hex($3));
    printf ("0x00000000%08x 0x%08x%08x\n", hex($1)+8,hex($4),hex($5));
  }
}

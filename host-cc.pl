#!/usr/bin/perl -w

$MIPS_HOME=$ENV{'MIPS_HOME'};
$objdump="mipseb-linux-objdump";
$as="mipseb-linux-as";
$cc="mipseb-linux-gcc ";
$image="$MIPS_HOME/genimage.pl";

use Getopt::Long;

my $opt_compile=0;
my $opt_output="";
my $verbose = 0;
my $keepfiles = 0;
my $raw_assembly = 0;
my $opt_include = "";
my $opt_dprototypes=-1;
my $dprototype_str = "";
my $opt_str = "";
my $v;

Getopt::Long::Configure("pass_through");
GetOptions(
	   "c" => \$opt_compile,
	   "o=s" => \$opt_output,
	   "v" => \$verbose,
	   "r" => \$raw_assembly,
           "k" => \$keepfiles,
	   "i=s" => sub { my( $n, $k, $v ) = @_;
                  $opt_include = $opt_include . "-I " . $k . " "
                  },
           "dprototypes=i" => \$opt_dprototypes
	  );

die "Usage: $0 [-c] [-k] [-v] [-o output] files...\n" unless $#ARGV >= 0;

#die "$0: -c and -o can only support one file argument" if ($opt_compile == 1 && $#ARGV != 0 && $opt_output ne "");

my $i;
my $type;

@objlist=();

if ($opt_dprototypes != -1) {
  $dprototype_str = "-DPROTOTYPES=" . $opt_dprototypes ;
}

for ($i=0; $i <= $#ARGV; $i++) {
  if ($ARGV[$i] =~ /^-/ && not ($ARGV[$i] =~ /^-(L|l)/)) {
    $opt_str = $opt_str . $ARGV[$i] . " "; 
  }
  elsif ($ARGV[$i] =~ /^(.+)\.([sc])$/) {
    $type = $2;
    if ($opt_output ne "") {
      if ($opt_compile == 0) {
	gen_obj_file ($ARGV[$i], $1 . ".o", $type);
	push (@objlist, $1 . ".o");
      }
      else {
	gen_obj_file ($ARGV[$i], $opt_output, $type);
      }
    }
    else {
      gen_obj_file ($ARGV[$i], $1 . ".o", $type);
      push (@objlist, $1 . ".o");
    }
  }
 else {
    push (@objlist, $ARGV[$i]);
  }
}

if ($opt_output eq "") {
  $opt_output = "a.out.image";
}


if ($opt_compile == 0) {
  link_obj_files ($opt_output . ".ld", @objlist);
  gen_image_file ($opt_output . ".ld", $opt_output);
  gen_inf_file ($opt_output . ".ld", $opt_output . ".inf");
  if ($keepfiles == 0) {
    if ($verbose) {
      printf ("unlink $opt_output" . ".ld\n");
    }
    unlink($opt_output . ".ld");
  }
}

exit 0;

sub gen_obj_file {

  my ($file,$output,$type) = @_;
  my $tmpfile;
  
  if($type eq "c") {
    print("Compiling and assembling $file\n");
    my_system($cc . " $opt_include -S -mno-abicalls -mno-branch-likely -static -mips1 $dprototype_str $opt_str $file -o tmp.$$.s");
    my_system($as . " -non_shared tmp.$$.s -o $output");
    my_system("rm -f tmp.$$.s");
  }
  elsif($type eq "s"){
    print("Assembling $file\n");
    my_system($as . " -non_shared $file -o $output");
  }
  else{
    print ("Illegal File Type. Must be .s or .c\n");
  }
  print("Generating $output\n");
}


sub link_obj_files {
  my $outfile = $_[0];
  
  shift;
  
  my @file = @_;
  
  if ($verbose) {
    printf ("Linking @file\n");
  }
    my_system($cc . "-Wl,--script=$MIPS_HOME/elf32btsmip.x,-static @file -o $outfile 2> .link.out ");
  
  if ( ! -f $outfile ) {
    print ("Linking failed. Please examine [.link.out]\n");
    exit (1);
 }
  unlink (".link.out");
}

sub my_system {
  my $cmd = $_[0];
  
  if ($verbose) {
    print $cmd . "\n";
  }
  system ($cmd);
}

sub gen_image_file {
  
    my ($infile, $outfile) = @_;
    my $entry_point;
    my $tmpfile;
    
    
      printf ("Generating image for $infile -> $outfile\n");
    
    if ($raw_assembly) {
      my_system ("$image $infile .text .data > $outfile");
    }
    else {
      my_system ("$image $infile > $outfile");
    }
  }
  
sub gen_inf_file {
  
  my ($infile, $outfile) = @_;
  my $entry_point;
  my $gp_val;

  printf ("Generating info file for $infile -> $outfile\n");
  die "Could not do objdump!\n" unless open (OBJDUMP, "$objdump -D $infile|");
  
  die "Could not open .inf file for writing!\n" unless open(INFO, ">$outfile");
  
  while (<OBJDUMP>) {
    if (/^(\S+) \<main\>/){
      $entry_point = $1 ;
    }
  }
  die "Could not find entry point. Yikes.\n" if (!defined ($entry_point));
  
  close (OBJDUMP);
  print INFO "0x$entry_point\n";
  close (INFO);
}

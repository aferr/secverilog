#!/usr/bin/perl

use Term::ANSIColor;

my $z3home ="/home/zhdf/z3/bin/external";
my $option = "smt2";
my $iverilog = "iverilog";

my $fail_counter = 0;
my $counter = 0;

sub print_ok {
  print colored("verified\n", 'green');
}

sub print_fail {
  print colored("fail\n", 'red');
}

# type check all files with .v extension in current directory
# first generate the z3 files
# my @files = <*>;
my @files = ("ddram.v", "dsram.v", "dtram.v", "idram.v", "isram.v", "itram.v", "alu.v", "bp.v", "ex.v", "if.v", "qc.v", "rd.v", "rf.v", "wb.v");
my $dep = "";
foreach my $file (@files) {
  if (-f $file and $file =~ /\.v$/) {
    # run iverilog to generate constraints
    print "Compiling file $file\n";
    `$iverilog -z $file`;
    $dep .= "$file ";
    #system ($iverilog, "-z", $file);
  }
}

print "Compiling file mem.v\n";
`$iverilog -z mem.v`;
$dep .= "mem.v ";

print "Compiling file cpu.v\n";
`$iverilog -z $dep cpu.v`;
$dep .= "cpu.v ";

my @files = <*>;
foreach my $file (@files) {
  if (-f $file and $file =~ /\.z3$/) {
    my ($prefix) = $file =~ m/(.*)\.z3$/;
    print "Verifying module $prefix ";

    # read the output of Z3
    my $str = `$z3home/z3 -$option $file`;
    
    # parse the input constraint file to identify assertions
    open(FILE, "$file") or die "Can't read file $file\n";
    my @assertions = ();
    my $assertion;
    my $isassertion = 0;
    $counter = 0;

    while (<FILE>) {
      if (m/^\(push\)/) {
        $assertion = "";
        $isassertion = 1;
      }
      elsif (m/^\(check-sat\)/) {
        push(@assertions, $assertion);
        $isassertion = 0;
      }
      elsif ($isassertion) {
        $assertion = $_;
      }
    }
    
    close (FILE);
    
    # find "unsat" assertions, and output the corrensponding comment in constraint source file
    my $errors = "";
    for(split /^/, $str) {
      if (/^sat/) {
        $assert = @assertions[$counter];
        $errors .= $assert;
	$fail_counter ++;
        $counter ++;
      }
      elsif (/^unsat/) {
        $counter ++;
      }
    }
    if ($errors eq "") {
      print_ok();
    }
    else {
      print_fail();
      print $errors;
    }
  }
}

print "Total: $fail_counter assertions failed\n";


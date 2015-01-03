#!/usr/bin/perl

# system ("./run.sh");
# no partitioned cache, mitigation off, mitigation on
@options = ("nopar", "mon");
@keys = ("key1", "key2");
print "Generating data ...\n";

foreach $key (@keys) {
  foreach $opt (@options) {
    $i=1;
    $printon=0;
    open INPUT , "<" . $opt . $key          or die $!;
    open OUT   , ">" . $opt . $key . ".dat" or die $!;

    printf OUT "#\ttime\n";
    while (<INPUT>) {
       if ($i==3) {
          $printon=1; 
       }
       if (/^decryption time: /) { 
          @cycles= m/^decryption time: (.*)$/;
          # the first two runs are used to initilize
          if ($printon) {
            printf OUT ("%d\t%d\t\n", $i, @cycles);
          }
          $i=$i+1;
       }
    }
  }
}

print "All data generated!\n";
# call gnuplot
print "Generating graph.\n";
system "gnuplot plotperformance.gnu";
system "gnuplot plotsize.gnu";

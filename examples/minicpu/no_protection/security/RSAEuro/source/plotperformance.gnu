set term postscript color enhanced
set output "rsa-performance.eps"
#set title "Execution time for different block sizes" offset 0,-1
set style fill solid 0.25 border
set key right bot
set xlabel "number of blocks decrypted"
set ylabel "decryption time \nin clock cycles (X10^{8})"
set xrange [1:10]
set yrange [0:]
set format y "%1.1t"
set xtics 1
set size 0.6,0.4

plot 'sys.dat'      u 1:2 title "sys"      with lines    lt 1 lw 3,  \
     ''             u 1:2 notitle          with points   lt 1 lw 3,  \
     'mon.dat'      u 1:2 title "mon"      with lines    lt 7 lw 3,  \
     ''             u 1:2 notitle          with points   lt 7 lw 3,  \
     'moff.dat'     u 1:2 title "moff"     with lines    lt 3 lw 3,  \
     ''             u 1:2 notitle          with points   lt 3 lw 3,  \
     'nopar.dat'    u 1:2 title "nopar"    with lines    lt 4 lw 3,  \
     ''             u 1:2 notitle          with points   lt 4 lw 3


!epstopdf rsa-performance.eps
#!evince result.pdf

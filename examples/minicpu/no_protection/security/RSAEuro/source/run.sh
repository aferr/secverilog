#!/bin/bash
SIMHOME="../../../../simplesim-3.0"
SAMPLEDIR="samples"
fname="rsademo"
onname="rsaon"
offname="rsaoff"
sysname="rsasys"
sample="allnames"
blocksize=(1 2 3 4 5 6 7 8 9 10)
/* options */
nopar="nopar"
moff="moff"
mon="mon"
sys="sys"

# turn mitigation on, and generate executable
rm *.o
cp mitigateon.h mitigate.h
cp rsa-inner.c rsa.c
make
cp $fname $onname 

# use system level mitigation
cp rsa-sys.c rsa.c
cp ../demo/rsademo-sys.c ../demo/rsademo.c
rm *.o
make
cp $fname $sysname

# turn mitigation off, and generate executable
cp rsa-inner.c rsa.c
cp ../demo/rsademo-inner.c ../demo/rsademo.c
rm *.o
cp mitigateoff.h mitigate.h
make
cp $fname $offname 

# use key2 
cp rsa-inner.c rsa.c
cp ../demo/rsademo-key2.c ../demo/rsademo.c
rm *.o
make
cp $fname $key2name 

#rm $nopar* $moff* $mon*

# use this code to generate all encrypted samples
# NOTICE: change ../demo/rsademo.c into encryption mode before executing this piece of script
# for item in ${blocksize[*]}
# do
#   echo "generating encrypted block with size $item"
#   $SIMHOME/sim-outorder -redir:sim log $offname $SAMPLEDIR/sample$item $SAMPLEDIR/sampleen$item
#   rm log
# done

for item in ${blocksize[*]}
do
   echo "executing with no partitioned cache"
   $SIMHOME/sim-outorder -lsq:size 2 -bpred perfect -decode:width 1 -issue:width 1 -commit:width 1 -fetch:ifqsize 1 -redir:sim log1 -redir:prog out1 -cache:dl1 dl1:128:32:4:l -cache:dl2 dl2:1024:64:4:l -cache:il1 il1:512:32:1:l -cache:il2 il2:1024:64:4:l -tlb:itlb itlb:16:4096:4:l -tlb:dtlb dtlb:32:4096:4:l $offname $SAMPLEDIR/sampleen$item $SAMPLEDIR/samplede$item
   cat out1 >> $nopar$item
  
   echo "executing with partitioned cache, but no mitiation"
   $SIMHOME/sim-parcache -lsq:size 2 -bpred perfect -decode:width 1 -issue:width 1 -commit:width 1 -fetch:ifqsize 1 -redir:sim log2 -redir:prog out2 -cache:dl1 dl1:64:32:4:l -cache:dl2 dl2:512:64:4:l -cache:il1 il1:256:32:1:l -cache:il2 il2:512:64:4:l -tlb:itlb itlb:8:4096:4:l -tlb:dtlb dtlb:16:4096:4:l $offname $SAMPLEDIR/sampleen$item $SAMPLEDIR/samplede$item
   cat out2 >> $moff$item
  
   echo "executing with partitioned cache, also with mitiation"
   $SIMHOME/sim-parcache -lsq:size 2 -bpred perfect -decode:width 1 -issue:width 1 -commit:width 1 -fetch:ifqsize 1 -redir:sim log3 -redir:prog out3 -cache:dl1 dl1:64:32:4:l -cache:dl2 dl2:512:64:4:l -cache:il1 il1:256:32:1:l -cache:il2 il2:512:64:4:l -tlb:itlb itlb:8:4096:4:l -tlb:dtlb dtlb:16:4096:4:l $onname $SAMPLEDIR/sampleen$item $SAMPLEDIR/samplede$item
   cat out3 >> $mon$item
   
   echo "executing with partitioned cache, system level mitiation"
   $SIMHOME/sim-parcache -lsq:size 2 -bpred perfect -decode:width 1 -issue:width 1 -commit:width 1 -fetch:ifqsize 1 -redir:sim log4 -redir:prog out4 -cache:dl1 dl1:64:32:4:l -cache:dl2 dl2:512:64:4:l -cache:il1 il1:256:32:1:l -cache:il2 il2:512:64:4:l -tlb:itlb itlb:8:4096:4:l -tlb:dtlb dtlb:16:4096:4:l $sysname $SAMPLEDIR/sampleen$item $SAMPLEDIR/samplede$item
   cat out4 >> $sys$item

   rm log1 log2 log3 log4 out1 out2 out3 out4
done
echo "Simulation done!"

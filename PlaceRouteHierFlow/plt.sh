#start=$1
#end=$200

for((i=0;i<201;i=i+10));do 
gnuplot $i.plt 
done 

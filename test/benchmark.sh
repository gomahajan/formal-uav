#!/bin/bash
#echo "b  q   time"

rm -f /tmp/mtime.$$

for ((i = 0 ; i <= 100 ; i += 10))
do
  for ((j = 0 ; j <= 100 ; j += 10))
  do
    for x in {1..10}
    do
      /usr/bin/time -f "real %e user %U sys %S" -a -o /tmp/mtime.$$ stack exec -- uav smt/uav_dreal
      tail -1 /tmp/mtime.$$
    done
    echo -n "b = $i  q = $j  " >> eval_stats
    #awk '{ et += $2; ut += $4; st += $6; count++ } END {  printf "Average:\nreal %.3f user %.3f sys %.3f\n", et/count, ut/count, st/count }' /tmp/mtime.$$ >> eval_stats
    awk '{ et += $2; ut += $4; st += $6; count++ } END {  printf "%.3f\n", st/count }' /tmp/mtime.$$ >> eval_stats
  done
done

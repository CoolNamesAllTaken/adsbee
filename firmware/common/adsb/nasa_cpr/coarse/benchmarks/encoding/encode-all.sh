#!/bin/bash

for csvfile in *.csv
do
   if [ -e "$csvfile" ]; then 
      ./encode $csvfile > $csvfile.out

      echo "$csvfile encoded into $csvfile.out"
   else 
      echo 'Warning: No *.csv file found in the current directory.'
   fi
done

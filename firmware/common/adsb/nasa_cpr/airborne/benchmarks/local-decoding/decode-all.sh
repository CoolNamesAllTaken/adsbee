#!/bin/bash

for csvfile in *.csv
do
   if [ -e "$csvfile" ]; then 
      ./decode $csvfile > $csvfile.out

      echo "$csvfile decoded into $csvfile.out"
   else 
      echo 'Warning: No *.csv file found in the current directory.'
   fi
done
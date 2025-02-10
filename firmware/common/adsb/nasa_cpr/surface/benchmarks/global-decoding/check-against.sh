#!/bin/bash

for csvfile in *.csv
do
   if [ -e "$csvfile" ]; then 
      DIFF=$(diff $csvfile $csvfile.out) 
      if [ "$DIFF" != "" ]
      then
         echo "Error in $csvfile"
      else 
         echo "$csvfile encoded as expected."
      fi
   else 
      echo 'Warning: No *.csv file found in the current directory.'
   fi
done
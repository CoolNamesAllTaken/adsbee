#!/bin/bash

for csvfile in *.csv
do
   if [ -e "$csvfile" ]; then 
      ./encode $csvfile > $csvfile.out

      ./check-encoding $csvfile $csvfile.out

      retVal=$?
      if [ $retVal -eq 0 ]; then
         echo "$csvfile encoded as expected."
      fi
   else 
      echo 'Warning: No *.csv file found in the current directory.'
   fi
done
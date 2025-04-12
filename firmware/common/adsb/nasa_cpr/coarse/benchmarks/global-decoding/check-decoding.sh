#!/bin/bash

for csvfile in *.csv
do
   if [ -e "$csvfile" ]; then 
      ./check-decoding $csvfile.out

      retVal=$?
      if [ $retVal -eq 0 ]; then
         echo "$csvfile decoded as expected."
      fi
   else 
      echo 'Warning: No *.csv file found in the current directory.'
   fi
done
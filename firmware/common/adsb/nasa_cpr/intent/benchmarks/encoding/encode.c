/* 
 * encode.c
 *
 * Contact: Cesar Munoz
 * Organization: NASA/Langley Research Center
 *
 * This software may be used, reproduced, and provided to others only as 
 * permitted under the terms of the agreement under which it was acquired from
 * the U.S. Government. Neither title to, nor ownership of, the software is 
 * hereby transferred. This notice shall remain on all copies of the software.
 * 
 * Copyright 2019 United States Government as represented by the Administrator
 * of the National Aeronautics and Space Administration. All Rights Reserved.
 * 
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../../cpr.h"

#define INPUT_LINE_MAX_LENGTH 100

#define __print_usage__ \
  fprintf(stderr,"USAGE: this program expects as argument the name of an CSV file.\n");\
  fprintf(stderr,"       Each line of such file must start with the following fields:\n");\
  fprintf(stderr,"          <latitude (AWB)>, <longitude (AWB)>\n");\
  fprintf(stderr,"       For intent messages, the format is always even (i=0).\n");

int main(int argc, char * argv[]){
    FILE *fp ;
    char line[INPUT_LINE_MAX_LENGTH] ;
    const char* token = NULL;
    int_type awb_lat, awb_lon;

    if(argc <= 1) {
        fprintf(stderr, "Error: Missing input file name.\n");
        __print_usage__;
        return 1;
    }

    fp = fopen(argv[1], "r");
    if(fp == NULL) {
        fprintf(stderr, "Error: File %s not found.\n", argv[1]);
        return 1;
    }

    char* tmp = NULL;
    while( fgets ( line, INPUT_LINE_MAX_LENGTH, fp ) != NULL ) {
        tmp = strdup(line);
        token = strtok(tmp, ",");
        awb_lat = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        awb_lon = (int_type) strtoul(token,NULL,16);
        free(tmp);

        struct message msg = encode(awb_lat, awb_lon);

        printf("%X,%X,%X,%X\n", awb_lat, awb_lon, msg.yz, msg.xz);
    }
    fclose(fp) ;
    return 0;
}
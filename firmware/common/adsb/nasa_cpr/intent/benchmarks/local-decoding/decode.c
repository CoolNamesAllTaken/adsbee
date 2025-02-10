/* 
 * decode.c
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

#define INPUT_LINE_MAX_LENGTH 200

#define __usage_str__ \
  "USAGE: this program expect as argument the name of an CSV file.\n"\
  "       Each line of the file must start with the following fields:\n"\
  "        1) reference latitude in degrees (double),\n"\
  "        2) reference longitude in degrees (double),\n"\
  "        3) reference latitude as AWB (unsigned int),\n"\
  "        4) reference longitude as AWB (unsigned int),\n"\
  "        5) current latitude in degrees (double),\n"\
  "        6) current longitude in degrees (double),\n"\
  "        7) current latitude as AWB (unsigned int),\n"\
  "        8) current longitude as AWB (unsigned int),\n"\
  "        9) message latitude [YZ] (unsigned int),\n"\
  "       10) message longitude [XZ] (unsigned int).\n"

int main(int argc, char * argv[]){
    FILE *fp ;
    char line[INPUT_LINE_MAX_LENGTH] ;
    const char* token = NULL;
    int_type awb_ref_lat, awb_ref_lon;
    int_type awb_cur_lat, awb_cur_lon;
    int_type encoded_lat, encoded_lon;
    int_type decoded_lat, decoded_lon;

    if(argc <= 1) {
        fprintf(stderr, "Error: Missing input file name.\n");
        fprintf(stderr, __usage_str__);
        return 1;
    }

    fp = fopen(argv[1], "r");
    if(fp == NULL) {
        fprintf(stderr, "Error: File %s not found.\n", argv[1]);
        fprintf(stderr, __usage_str__);
        return 1;
    }

    char* tmp = NULL;
    while( fgets ( line, INPUT_LINE_MAX_LENGTH, fp ) != NULL ) {
        tmp = strdup(line);
        token = strtok(tmp, ",");
        awb_ref_lat = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        awb_ref_lon = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        awb_cur_lat = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        awb_cur_lon = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        encoded_lat = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        encoded_lon = (int_type) strtoul(token,NULL,16);
        free(tmp);

        struct message msg = { 0, encoded_lat, encoded_lon};

        struct recovered_position r_pos = local_dec(awb_ref_lat, awb_ref_lon, msg);

        printf("%X,%X,%X,%X,%X,%X,%X,%X\n", 
                awb_ref_lat, awb_ref_lon, 
                awb_cur_lat, awb_cur_lon, 
                encoded_lat, encoded_lon, r_pos.lat_awb, r_pos.lon_awb);
    }
    fclose(fp) ;
    return 0;
}
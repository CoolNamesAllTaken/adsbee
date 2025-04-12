/* 
 * check-encoding.c
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
#include <math.h>
#include "../../cpr.h"

#define INPUT_LINE_MAX_LENGTH 270

int main(int argc, char * argv[]){
    int result = 0; // OK
    int i;
    unsigned int line_number = 0;
    FILE *original_data_file ;
    FILE *result_data_file ;
    char line[INPUT_LINE_MAX_LENGTH] ;
    const char* token = NULL;
    int_type expected_encoded_lat, expected_encoded_lon;
    int_type result_encoded_lat, result_encoded_lon;

    if(argc <= 1) {
        fprintf(stderr, "Error: Missing input file names.\n");
        return 1;
    }

    original_data_file = fopen(argv[1], "r");
    if(original_data_file == NULL) {
        fprintf(stderr, "Error: File %s not found.\n", argv[1]);
        return 1;
    }

    result_data_file = fopen(argv[2], "r");
    if(result_data_file == NULL) {
        fprintf(stderr, "Error: File %s not found.\n", argv[2]);
        return 1;
    }

    char* tmp = NULL;
    while( result != 0 && fgets ( line, INPUT_LINE_MAX_LENGTH, original_data_file ) != NULL ) {
        tmp = strdup(line);

        token = strtok(tmp, ",");
        // format 
        token = strtok(NULL, ",");
        // awb_lat
        token = strtok(NULL, ",");
        // awb_lon
        token = strtok(NULL, ",");
        expected_encoded_lat = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        expected_encoded_lon = (int_type) strtoul(token,NULL,16);

        if ( fgets ( line, INPUT_LINE_MAX_LENGTH, result_data_file ) != NULL ) {

            token = strtok(tmp, ",");
            // format 
            token = strtok(NULL, ",");
            // awb_lat
            token = strtok(NULL, ",");
            // awb_lon
            token = strtok(NULL, ",");
            result_encoded_lat = (int_type) strtoul(token,NULL,16);
            token = strtok(NULL, ",");
            result_encoded_lon = (int_type) strtoul(token,NULL,16);

            line_number++;

            if(expected_encoded_lat != result_encoded_lat) {
                printf("Error in line %d: expected latitude is %X but computed latitude is %X.\n",line_number,expected_encoded_lat,result_encoded_lat);
                result=1; // ERROR
            }

            if(expected_encoded_lon != result_encoded_lon) {
                printf("Error in line %d: expected longitude is %X but computed longitude is %X.\n",line_number,expected_encoded_lon,result_encoded_lon);
                result=1; // ERROR
            }

        } else {
            printf("File %s has more rows than %s.\n",argv[1],argv[2]);
            result = 1; // ERROR
        }

        free(tmp);
    }
    fclose(original_data_file) ;
    return result;
}
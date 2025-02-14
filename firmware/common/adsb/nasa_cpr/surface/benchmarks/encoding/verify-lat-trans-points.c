/* 
 * verify-lat-trans-points.c
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
    FILE *fp ;
    char line[INPUT_LINE_MAX_LENGTH] ;
    const char* token = NULL;
    int_type awb_lat_low, awb_lat_up;
    int_type enc_lat_up, enc_lon_up;
    int_type enc_lat_low, enc_lon_low;
    double deg_lat_low, deg_lat_up;

    // For this test, the input longitude value should be set to 45 degrees (0x20000000 AWB).
    int_type awb_lon = 0x20000000;

    if(argc <= 1) {
        fprintf(stderr, "Error: Missing input file name.\n");
        return 1;
    }

    fp = fopen(argv[1], "r");
    if(fp == NULL) {
        fprintf(stderr, "Error: File %s not found.\n", argv[1]);
        return 1;
    }

    char* tmp = NULL;
    while( result == 0 && fgets ( line, INPUT_LINE_MAX_LENGTH, fp ) != NULL ) {
        tmp = strdup(line);

        token = strtok(tmp, ",");
        // lower latitude in degrees
        deg_lat_low = atof(token);
        token = strtok(NULL, ",");
        // lower latitude as AWB
        awb_lat_low = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        // upper latitude in degrees
        deg_lat_up = atof(token);
        token = strtok(NULL, ",");
        // upper latitude as AWB
        awb_lat_up = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        // encoding for the latitude of the lower position
        enc_lat_low = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        // encoding for the longitude of the lower position
        enc_lon_low = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        // encoding for the latitude of the upper position
        enc_lat_up = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        // encoding for the longitude of the upper position
        enc_lon_up = (int_type) strtoul(token,NULL,16);

        free(tmp);

        // Step 1: the lower position is encoded. The test is considered failed if the 
        //         encoded message does not match the expected message for the lower 
        //         latitude (this test is stricter that the one described in the MOPS).
        struct message msg_low = encode(0, awb_lat_low, awb_lon);

        if(msg_low.yz == enc_lat_low){

            // Step 2: the upper position is encoded. The test is considered failed if 
            //         the encoded message does not match the expected message for the 
            //         lower latitude (this test is stricter that the one described in 
            //         the MOPS).
            struct message msg_up = encode(0, awb_lat_up, awb_lon);

            if(msg_up.yz == enc_lat_up){

                // Step 3: Starting at the lower position, the value of the AWB 
                //         latitude is incremented by one until the value of the upper
                //         AWB latitude is reached. The test is considered passed only
                //         if the encoded position change exactly one time, starting 
                //         in the lower message and ending in the upper message.
                int_type awb_lat = awb_lat_low;

                int stage = 0; // Stage==0 means that the encoded message for the 
                               // current position agrees with the lower message. 
                               // Stage==1 means that the encoded message for the 
                               // current position agrees with the upper message. 

                while(result==0 && awb_lat < awb_lat_up){
                    awb_lat++;
                    struct message msg = encode(0, awb_lat, awb_lon);
                    if(stage==0){
                        if(!(msg.xz == msg_low.xz && msg.yz == msg_low.yz)){
                            if(msg.xz == msg_up.xz && msg.yz == msg_up.yz) stage++;
                            else {
                                printf("Encoded message changed from lower to unknown.\n");
                                result = 1; // ERROR
                            }
                        } 
                    } else {
                        if(!(msg.xz == msg_up.xz && msg.yz == msg_up.yz)){
                            printf("Encoded message changed from upper to unknown.\n");
                            result = 1; // ERROR
                        }
                    }
                }
                if(stage != 1){
                    printf("Encoded message did not reach upper message.\n");
                    result = 1; // ERROR
                }
            } else {
                printf("Upper latitude encoded incorrectly (expected: %X, actual: %X)\n",enc_lat_up,msg_up.yz);
                result = 1; // ERROR
            }
        } else {
            printf("Lower latitude encoded incorrectly (expected: %X, actual: %X)\n",enc_lat_low,msg_low.yz);
            result = 1; // ERROR
        }
    }

    if(result==0) printf("Test passed.\n");

    fclose(fp) ;
    return result;
}
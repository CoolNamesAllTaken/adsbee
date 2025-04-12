/* 
 * check-decoding.c
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

#define INPUT_LINE_MAX_LENGTH 200

// dlat
#define __dlati__(i) (i==0?6.0:(360.0/59.0))

// dlon
#define __dlon__(i,awblat) (nl_awb(rlat_int(i,awblat))-i>0?360.0/(nl_awb(rlat_int(i,awblat))-i):360.0)

#define P2_13 8192.0
#define P2_18 262144.0
#define P2_20 1048576.0

// P2_NB1 = 2^(max(17,NB)+1)
#if NB==12
#define P2_NB1 P2_13
#elif NB==17
#define P2_NB1 P2_18
#elif NB==19
#define P2_NB1 P2_20 
#else
unknown_NB_value;
#endif

#define RESOLUTION 360.0/4294967296.0 // = 360/2^32
#define INV_RESOLUTION 4294967296.0/360.0 // = 2^32/360

// simple in-line abs(X-Y)
#define __diffabs__(X,Y) (X>=Y?X-Y:Y-X)
// simple modulus operation (correct for X in [-359,(2*360-1)])
#define __mod360__(X) (X>=360?X-360:(X<0?360+X:X))

double awb2lat(int_type awb_lat){
    if(awb_lat<=1073741824) // 2^30
        return awb_lat*RESOLUTION;
    else 
        return awb_lat*RESOLUTION - 360.0;
}

double awb2lon(int_type awb_lon){
    return __mod360__(awb_lon*RESOLUTION);
}

int_type lat2awb(double lat){
    return (int_type)floor(INV_RESOLUTION*__mod360__(lat)+0.5);
}

int_type lon2awb(double lon){
    return (int_type)floor(lon*INV_RESOLUTION+0.5);
}


#define __close_mod_le_360__(a,b,eps) (__mod360__(a-b) <= eps) || (__mod360__(a-b) >= 360 - eps)

int main(int argc, char * argv[]){
    int result = 0; // OK
    int i;
    FILE *fp ;
    char line[INPUT_LINE_MAX_LENGTH] ;
    const char* token = NULL;
    int_type awb_ref_lat, awb_ref_lon;
    int_type awb_cur_lat, awb_cur_lon;
    int_type awb_rec_lat, awb_rec_lon;
    int_type encoded_lat, encoded_lon;
    int_type decoded_lat, decoded_lon;
    double deg_ref_lat, deg_ref_lon;
    double deg_cur_lat, deg_cur_lon;
    int_type awb_dist;

    if(argc <= 1) {
        fprintf(stderr, "Error: Missing input file name.\n");
        return 1;
    }

    fp = fopen(argv[1], "r");
    if(fp == NULL) {
        fprintf(stderr, "Error: File %s not found.\n", argv[1]);
        return 1;
    }

    // Bound stated by the local_correctness_theorem
    int_type awb_bound;
    int_type awb_bound_i0 = lat2awb(__dlati__(0)/P2_NB1);
    int_type awb_bound_i1 = lat2awb(__dlati__(1)/P2_NB1);

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
        i = atoi(token);
        token = strtok(NULL, ",");
        encoded_lat = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        encoded_lon = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        awb_rec_lat = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        awb_rec_lon = (int_type) strtoul(token,NULL,16);
        free(tmp);

        deg_cur_lat = awb2lat(awb_cur_lat);
        awb_bound = (i==0?awb_bound_i0:awb_bound_i1);
        double deg_rec_lat = awb2lat(awb_rec_lat);
        awb_dist = __diffabs__(awb_cur_lat,awb_rec_lat);
        if(awb_dist > awb_bound) {
            printf("Latitude -> recovered: %.20f and actual: %.20f at %u (vs. %u)\n",deg_rec_lat,deg_cur_lat,awb_dist,awb_bound);
            result = 1; // ERROR
        }
        
        #if NB==19
        deg_cur_lon = awb2lon(awb_cur_lon);
        double deg_bound = __dlon__(i,awb_cur_lat)/P2_NB1;
        awb_bound = lon2awb(deg_bound);
        double deg_rec_lon = awb2lon(awb_rec_lon);
        awb_dist = __diffabs__(awb_cur_lon,awb_rec_lon);
        if(!(__close_mod_le_360__(deg_rec_lon,deg_cur_lon,__dlon__(i,awb_cur_lat)/P2_NB1))) {
            printf("Longitude -> recovered: %.20f (%X) and actual: %.20f (%X) at %.20f (vs. %.20f)\n",deg_rec_lon,awb_rec_lon,deg_cur_lon,awb_cur_lon,deg_rec_lon-deg_cur_lon,__dlon__(i,awb_cur_lat));
            result = 1; // ERROR
        }
        #else
        deg_cur_lon = awb2lon(awb_cur_lon);
        awb_bound = lon2awb(__dlon__(i,awb_cur_lat)/P2_NB1);
        double deg_rec_lon = awb2lon(awb_rec_lon);
        awb_dist = __diffabs__(awb_cur_lon,awb_rec_lon);
        if(awb_dist > awb_bound) {
            printf("Longitude -> recovered: %.20f (%X) and actual: %.20f (%X) at %u (vs. %u)\n",deg_rec_lon,awb_rec_lon,deg_cur_lon,awb_cur_lon,awb_dist,awb_bound);
            result = 1; // ERROR
        }
        #endif
    }
    fclose(fp) ;
    return result;
}
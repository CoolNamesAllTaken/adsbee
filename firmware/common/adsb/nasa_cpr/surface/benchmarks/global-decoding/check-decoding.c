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
#define __dlati__(i) (i==0?1.5:(90.0/59.0))

// dlon
#define __dlon__(i,lat) (nl_awb(lat2awb(lat))-i>0?360.0/(nl_awb(lat2awb(lat))-i):360.0)

#define P2_13 8192.0
#define P2_18 262144.0
#define P2_19 524288.0
#define P2_20 1048576.0

// P2_NB1 = 2^(max(17,NB)+1)
#define P2_NB1 P2_18 

#define RESOLUTION 360.0/4294967296.0 // = 360/2^32
#define INV_RESOLUTION 4294967296.0/360.0 // = 2^32/360

double awb2lat(int_type awb_lat){
    if(awb_lat<=1073741824) // 2^30
        return awb_lat*RESOLUTION;
    else 
        return awb_lat*RESOLUTION - 360.0;
}

// simple in-line abs(X-Y)
#define __diffabs__(X,Y) ((unsigned long)X>=(unsigned long)Y?X-Y:Y-X)

// simple modulus operation (correct for X in [-359,(2*360-1)])
#define __mod360__(X) (X>=360?X-360:(X<0?360+X:X))
#define __mod90__(X) (X<0?90+X:(X>=90?X-90:X))

int_type lat2awb(double lat){
    return (int_type)floor(INV_RESOLUTION*__mod360__(lat)+0.5);
}

int_type lon2awb(double lon){
    return (int_type)floor(lon*INV_RESOLUTION+0.5);
}

// LATi is supposed to be recovered lat i (in degrees)
#define __lon_enc_bound_surf__(LAT0,LAT1) (nl_awb(lat2awb(LAT0))==1?45:(__dlon__(1,LAT1)-__dlon__(0,LAT0))/8.0-__dlon__(1,LAT1)/P2_19)

#define __longitude_correctly_decoded__(LON0,LON1,EPS) (__mod90__(LON0-LON1) <= EPS) || (__mod90__(LON0-LON1) >= 360 - EPS)



int main(int argc, char * argv[]){
    int result = 0; // OK
    int i;
    FILE *fp ;
    char line[INPUT_LINE_MAX_LENGTH] ;
    const char* token = NULL;
    int_type awb_evn_lat, awb_evn_lon;
    int_type awb_odd_lat, awb_odd_lon;
    int_type enc_evn_lat, enc_evn_lon;
    int_type enc_odd_lat, enc_odd_lon;
    double deg_evn_lat, deg_evn_lon;
    double deg_odd_lat, deg_odd_lon;
    int_type dec_evn_lat, dec_evn_lon;
    int_type dec_odd_lat, dec_odd_lon;
    int nl_match;

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
        awb_evn_lat = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        awb_evn_lon = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        enc_evn_lat = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        enc_evn_lon = (int_type) strtoul(token,NULL,16);

        token = strtok(NULL, ",");
        awb_odd_lat = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        awb_odd_lon = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        enc_odd_lat = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        enc_odd_lon = (int_type) strtoul(token,NULL,16);

        token = strtok(NULL, ",");
        nl_match = atoi(token);
        token = strtok(NULL, ",");
        dec_evn_lat = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        dec_evn_lon = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        dec_odd_lat = (int_type) strtoul(token,NULL,16);
        token = strtok(NULL, ",");
        dec_odd_lon = (int_type) strtoul(token,NULL,16);

        free(tmp);

        deg_evn_lat = awb2lat(awb_evn_lat);
        deg_evn_lat = __mod90__(deg_evn_lat);
        awb_evn_lat = lat2awb(deg_evn_lat);

        deg_odd_lat = awb2lat(awb_odd_lat);
        deg_odd_lat = __mod90__(deg_odd_lat);
        awb_odd_lat = lat2awb(deg_odd_lat);

        double deg_dec_evn_lat = awb2lat(dec_evn_lat);
        int_type evn_awb_dist = __diffabs__(awb_evn_lat,dec_evn_lat);
        if(evn_awb_dist > awb_bound_i0) {
            printf("EVEN Latitude recovered: %.20f (%X) and actual: %.20f (%X) at %u (vs. %u)\n",deg_dec_evn_lat,dec_evn_lat,deg_evn_lat,awb_evn_lat,evn_awb_dist,awb_bound_i0);
            result = 1; // ERROR
        }

        double deg_dec_odd_lat = awb2lat(dec_odd_lat);
        int_type odd_awb_dist = __diffabs__(awb_odd_lat,dec_odd_lat);
        if(odd_awb_dist > awb_bound_i1) {
            printf("ODD Latitude recovered: %.20f and actual: %.20f at %u (vs. %u)\n",deg_dec_odd_lat,deg_odd_lat,odd_awb_dist,awb_bound_i1);
            result = 1; // ERROR
        }

        deg_evn_lon = awb2lat(awb_evn_lon);
        deg_evn_lon = __mod90__(deg_evn_lon);
        awb_evn_lon = lat2awb(deg_evn_lon);

        int_type awb_lon_bound_evn = lon2awb(__lon_enc_bound_surf__(deg_dec_evn_lat,deg_dec_odd_lat));

        double deg_dec_evn_lon = awb2lat(dec_evn_lon);
        if(!(__longitude_correctly_decoded__(deg_evn_lon,deg_dec_evn_lon,awb_lon_bound_evn))){
            printf("EVEN Longitude recovered: %.20f (%X) and actual: %.20f (%X) at %u (bound %u)\n",deg_dec_evn_lon,dec_evn_lon,deg_evn_lon,awb_evn_lon,__diffabs__(awb_evn_lon,dec_evn_lon),awb_lon_bound_evn);
            result = 1; // ERROR
        }

        deg_odd_lon = awb2lat(awb_odd_lon);
        deg_odd_lon = __mod90__(deg_odd_lon);
        awb_odd_lon = lat2awb(deg_odd_lon);

        int_type awb_lon_bound_odd = lon2awb(__lon_enc_bound_surf__(deg_dec_odd_lat,deg_dec_odd_lat));

        double deg_dec_odd_lon = awb2lat(dec_odd_lon);
        if(!(__longitude_correctly_decoded__(deg_odd_lon,deg_dec_odd_lon,awb_lon_bound_odd))){
            printf("ODD Longitude recovered: %.20f (%X) and actual: %.20f (%X) at %u (bound %u)\n",deg_dec_odd_lon,dec_odd_lon,deg_odd_lon,awb_odd_lon,__diffabs__(awb_odd_lon,dec_odd_lon),awb_lon_bound_odd);
            result = 1; // ERROR
        }
    }
    fclose(fp) ;
    return result;
}
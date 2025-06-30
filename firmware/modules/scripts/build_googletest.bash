#!/bin/bash
# This script builds the Google Test framework from source. Run it from the root of the adsbee repository in the pico-docker container.
cd /adsbee/modules/googletest
rm -rf build
mkdir build
cd build
cmake cmake -DBUILD_SHARED_LIBS=ON ..
make
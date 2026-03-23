#!/bin/bash
# This script builds the TI docker image for the firmware build.

# Specify build for AMD64 architecture so that we don't get rosetta errors in images that are built on Apple Silicon.
docker build -t coolnamesalltaken/ti-lpf2:latest --file Dockerfile --platform linux/amd64 .
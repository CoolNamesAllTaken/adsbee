#!/bin/bash

# Usage: ./record_tcp.bash <local-port> <output-file>
# Example: ./record_tcp.bash 12345 output.pcap

# Records a TCP port using socat and saves the output to a file. Defaults to making the filename
# the current timestamp if not provided.

LOCAL_PORT=$1
OUTPUT_FILE=$(dirname $0)/recordings/${2:-$(date +%Y%m%d_%H%M%S).txt}

echo "Recording TCP port $LOCAL_PORT to file $OUTPUT_FILE"

# Start recording the TCP port using socat
socat -v TCP-LISTEN:$LOCAL_PORT,reuseaddr,fork OPEN:$OUTPUT_FILE,creat,append
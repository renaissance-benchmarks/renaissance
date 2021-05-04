#!/bin/bash
source "$(dirname "$0")/common.sh"

# Try running SBT in client mode. This will start the server and 
# leave it running to speed up subsequent invocations.
ci_sbt --client --batch about

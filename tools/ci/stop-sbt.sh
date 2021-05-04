#!/bin/bash
source "$(dirname "$0")/common.sh"

# Stop SBT server
ci_sbt --client --batch shutdown

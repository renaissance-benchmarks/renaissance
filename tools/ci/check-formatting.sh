#!/bin/bash
source "$(dirname "$0")/common.sh"

# Check that the source code is properly formatted
ci_sbt --client --batch renaissanceFormatCheck

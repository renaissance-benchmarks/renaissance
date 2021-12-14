#!/bin/bash
source "$(dirname "$0")/common.sh"

# Build the base bundle if missing
[ -s "$RENAISSANCE_JAR" ] || ci_sbt --batch 'renaissancePackage;renaissanceJmhPackage'

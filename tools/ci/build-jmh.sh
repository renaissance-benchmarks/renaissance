#!/bin/bash
source "$(dirname "$0")/common.sh"

# Build the JMH bundle if missing
[ -s "$RENAISSANCE_JMH_JAR" ] || ci_sbt --client --batch renaissanceJmh/jmh:assembly

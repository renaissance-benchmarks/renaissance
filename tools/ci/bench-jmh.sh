#!/bin/bash
source "$(dirname "$0")/common.sh"

# Test benchmarks under JMH harness, replacing incompatible benchmarks with 'dummy-empty'
java -Xms2500M -Xmx2500M -Dorg.renaissance.jmh.fakeIncompatible=true -jar "$RENAISSANCE_JMH_JAR" -wi 0 -i 1 -f 1 -foe true

#!/bin/bash
source "$(dirname "$0")/common.sh"

# Test benchmarks under JMH harness using the 'test' configuration
# and replacing incompatible benchmarks with 'dummy-empty'.

java -jar "$RENAISSANCE_JMH_JAR" \
	-jvmArgs -Xms2500M -jvmArgs -Xmx2500m \
	$( for arg in $( get_jvm_workaround_args ); do echo "-jvmArgs" "$arg"; done ) \
	-jvmArgs -Dorg.renaissance.jmh.configuration=test \
	-jvmArgs -Dorg.renaissance.jmh.fakeIncompatible=true \
	-wi 0 -i 1 -f 1 -foe true

#!/bin/bash
source "$(dirname "$0")/common.sh"

# Show the bundle cache directory
ls -1 "$CACHE_DIR"

# Get the base bundle from cache
if [ -s "$RENAISSANCE_JAR_CACHED" ]; then
	mkdir -p "$RENAISSANCE_DIR"
	cp_reflink "$RENAISSANCE_JAR_CACHED" "$RENAISSANCE_DIR"
fi

# Get the JMH bundle from cache
if [ -s "$RENAISSANCE_JMH_JAR_CACHED" ]; then
	mkdir -p "$RENAISSANCE_JMH_DIR"
	cp_reflink "$RENAISSANCE_JMH_JAR_CACHED" "$RENAISSANCE_JMH_DIR"
fi

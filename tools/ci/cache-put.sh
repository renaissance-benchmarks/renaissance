#!/bin/bash
source "$(dirname "$0")/common.sh"

# Clear bundle cache directory
mkdir -p "$CACHE_DIR"
find "$CACHE_DIR" -type f -name '*.jar' -print -delete

# Store bundles in the cache
[ -s "$RENAISSANCE_JAR" ] && cp_reflink "$RENAISSANCE_JAR" "${CACHE_DIR}"
[ -s "$RENAISSANCE_JMH_JAR" ] && cp_reflink "$RENAISSANCE_JMH_JAR" "${CACHE_DIR}"

# Show the bundle cache directory
ls -1 "$CACHE_DIR"

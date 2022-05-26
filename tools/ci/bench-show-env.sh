#!/bin/bash

set -uoe pipefail

source "$(dirname "$0")/common.sh"

set -x

java -Xms1g -Xmx1g -jar "$RENAISSANCE_JAR" -c test -r 1 --json - dummy-empty

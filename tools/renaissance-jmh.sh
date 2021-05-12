#!/bin/bash

BASE_DIR="$(dirname "$0")"
ROOT_DIR="$(git -C "$BASE_DIR" rev-parse --show-toplevel)"
RENAISSANCE_GIT_VERSION=$(git -C "$BASE_DIR" describe --dirty=-SNAPSHOT)
RENAISSANCE_VERSION=${RENAISSANCE_GIT_VERSION#v}

exec java $JAVA_OPTS -jar "$ROOT_DIR/renaissance-jmh/target/scala-2.12/renaissance-jmh-assembly-$RENAISSANCE_VERSION.jar" "$@"

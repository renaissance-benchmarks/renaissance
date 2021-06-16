#!/bin/bash

# Fail the script if any command fails
set -o errexit

# Print shell input lines as they are read.
# set -o verbose

# Trace variable expansion and command execution
# set -o xtrace

# Project root directory
ROOT_DIR="$(git rev-parse --show-toplevel || realpath "$( dirname "$0" )/../../" )"

# Cache directory for files we explicitly produce
CACHE_DIR="$HOME/.prebuilt"

# Raw version as produced by git
RENAISSANCE_GIT_VERSION=$(git describe --tags --always --dirty=-SNAPSHOT || echo "ci-SNAPSHOT" )

# Strip leading 'v' from the git-produced version
RENAISSANCE_VERSION=${RENAISSANCE_GIT_VERSION#v}

# The base bundle
RENAISSANCE_DIR="target"
RENAISSANCE_JAR_NAME="renaissance-gpl-${RENAISSANCE_VERSION}.jar"
RENAISSANCE_JAR_CACHED="${CACHE_DIR}/$RENAISSANCE_JAR_NAME"
RENAISSANCE_JAR="${RENAISSANCE_DIR}/$RENAISSANCE_JAR_NAME"

# The JMH bundle
RENAISSANCE_JMH_DIR="renaissance-jmh/target/scala-2.12"
RENAISSANCE_JMH_JAR_NAME="renaissance-jmh-assembly-${RENAISSANCE_VERSION}.jar"
RENAISSANCE_JMH_JAR_CACHED="${CACHE_DIR}/$RENAISSANCE_JMH_JAR_NAME"
RENAISSANCE_JMH_JAR="${RENAISSANCE_JMH_DIR}/$RENAISSANCE_JMH_JAR_NAME"

ci_sbt() {
	local TRUST_STORE="$ROOT_DIR/tools/jks/cacerts"
	tools/sbt/bin/sbt "-J-Djavax.net.ssl.trustStore=$TRUST_STORE" "$@"
}

cp_reflink() {
	[ "$OSTYPE" = "linux-gnu" ] && local REFLINK="--reflink=auto"
	cp $REFLINK "$@"
}


# Make sure we are in the top-level directory so that we can use
# relative paths when referring to files within the project.
pushd "$ROOT_DIR"

# Trace variable expansion and command execution
set -o xtrace

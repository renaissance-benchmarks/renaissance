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
RENAISSANCE_GIT_VERSION=$(git describe --tags --always --abbrev=7 --dirty=-SNAPSHOT || echo "ci-SNAPSHOT" )

# Strip leading 'v' from the git-produced version
RENAISSANCE_VERSION=${RENAISSANCE_GIT_VERSION#v}

# Try to guess JVM version (and replace 1.8 with 8)
# The awful splitting and use of 'NN*' instead of 'N\+' is because
# we need to support non-GNU sed too
RENAISSANCE_JVM_MAJOR_VERSION="$( java -version 2>&1 \
    | sed -n -e '/version[[:blank:]][[:blank:]]*"/{' -e 's/.*version[[:blank:]][[:blank:]]*"\([^"]*\)".*/\1/; s/1[.]8/8/; s/^\([^.]*\)[.].*/\1/; p' -e '}' \
    || echo 8 )"

# The base bundle
RENAISSANCE_DIR="target"
RENAISSANCE_JAR_NAME="renaissance-gpl-${RENAISSANCE_VERSION}.jar"
RENAISSANCE_JAR_CACHED="${CACHE_DIR}/$RENAISSANCE_JAR_NAME"
RENAISSANCE_JAR="${RENAISSANCE_DIR}/$RENAISSANCE_JAR_NAME"

# The JMH bundle
RENAISSANCE_JMH_DIR="renaissance-jmh/target"
RENAISSANCE_JMH_JAR_NAME="renaissance-jmh-${RENAISSANCE_VERSION}.jar"
RENAISSANCE_JMH_JAR_CACHED="${CACHE_DIR}/$RENAISSANCE_JMH_JAR_NAME"
RENAISSANCE_JMH_JAR="${RENAISSANCE_JMH_DIR}/$RENAISSANCE_JMH_JAR_NAME"

ci_sbt() {
	local TRUST_STORE="$ROOT_DIR/tools/jks/cacerts"
	$ROOT_DIR/tools/sbt/bin/sbt "-J-Djavax.net.ssl.trustStore=$TRUST_STORE" "$@"
}

cp_reflink() {
	[ "$OSTYPE" = "linux-gnu" ] && local REFLINK="--reflink=auto"
	cp $REFLINK "$@"
}

get_jvm_workaround_args() {
    case "$RENAISSANCE_JVM_MAJOR_VERSION" in
        16|17|18|19|20|21|22|23|24-ea|24)
            echo "--add-opens=java.base/java.lang=ALL-UNNAMED"
            echo "--add-opens=java.base/java.lang.invoke=ALL-UNNAMED"
            echo "--add-opens=java.base/java.lang.reflect=ALL-UNNAMED"
            echo "--add-opens=java.base/java.util=ALL-UNNAMED"
            echo "--add-opens=java.base/java.nio=ALL-UNNAMED"
            echo "--add-opens=java.base/jdk.internal.ref=ALL-UNNAMED"
            echo "--add-opens=java.base/sun.nio.ch=ALL-UNNAMED"
            echo "--add-opens=jdk.compiler/com.sun.tools.javac.file=ALL-UNNAMED"
            ;;
        *)
            ;;
    esac
}

if command -v timeout >/dev/null; then
    TIMEOUT_IMPL=timeout_with_thread_dump_real
else
    TIMEOUT_IMPL=timeout_with_thread_dump_fake
fi

timeout_with_thread_dump_real() {
    timeout --signal=3 --kill-after=5s "$@"
}
timeout_with_thread_dump_fake() {
    shift
    "$@"
}
timeout_with_thread_dump() {
    "$TIMEOUT_IMPL" "$@"
}


# Make sure we are in the top-level directory so that we can use
# relative paths when referring to files within the project.
pushd "$ROOT_DIR"

# Trace variable expansion and command execution
set -o xtrace

#!/bin/sh

set -ueo pipefail

msg() {
    echo "[build-ubench-agent]:" "$@" >&2
}

UBENCH_AGENT_COMMIT="7b315c99b2bb6d32ce436d5b471172850e0803d8"
UBENCH_AGENT_TARBALL="java-ubench-agent-$UBENCH_AGENT_COMMIT.tar.gz"
UBENCH_AGENT_TARBALL_URL="https://github.com/D-iii-S/java-ubench-agent/archive/$UBENCH_AGENT_COMMIT.tar.gz"
UBENCH_AGENT_DIR="java-ubench-agent-$UBENCH_AGENT_COMMIT"

msg "Fetching sources..."
if wget --version >/dev/null 2>&1; then
    wget --continue -O "$UBENCH_AGENT_TARBALL" "$UBENCH_AGENT_TARBALL_URL"
else
    curl --continue-at - --location -o "$UBENCH_AGENT_TARBALL" "$UBENCH_AGENT_TARBALL_URL"
fi
if ! [ -d "$UBENCH_AGENT_DIR" ]; then
    msg "Unpacking the tarball..."
    tar xzf "$UBENCH_AGENT_TARBALL"
fi

msg "Building agent..."
pushd "$UBENCH_AGENT_DIR"
ant -Dant.build.javac.source=1.8 -Dant.build.javac.target=1.8 lib
msg "Build succeeded."
popd

AGENT_NATIVE_FILE=`find $UBENCH_AGENT_DIR/out/lib -name '*agent*' | grep -v '\.jar$'`

msg "Copying agent files..."
cp -f "$AGENT_NATIVE_FILE" .
cp -f "$UBENCH_AGENT_DIR/out/lib/ubench-agent.jar" lib

AGENT_NATIVE_FILE=$( realpath $( basename $AGENT_NATIVE_FILE ) )

msg "Add the following to Java command line when starting the suite:"
msg "  -agentpath:$AGENT_NATIVE_FILE"

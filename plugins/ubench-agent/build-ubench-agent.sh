#!/bin/sh

set -ueo pipefail

msg() {
    echo "[build-ubench-agent]:" "$@" >&2
}

UBENCH_AGENT_DIR="ubench-agent-repo"

msg "Fetching sources..."
if ! [ -d "$UBENCH_AGENT_DIR" ]; then
    git clone https://github.com/D-iii-S/java-ubench-agent.git "$UBENCH_AGENT_DIR"
else
    ( cd "$UBENCH_AGENT_DIR"; git pull )
fi

msg "Building agent..."
pushd "$UBENCH_AGENT_DIR"
ant lib
msg "Build succeeded."
popd

AGENT_NATIVE_FILE=`find $UBENCH_AGENT_DIR/out/lib -name '*agent*' | grep -v '\.jar$'`

msg "Copying agent files..."
cp -f "$AGENT_NATIVE_FILE" .
cp -f "$UBENCH_AGENT_DIR/out/lib/ubench-agent.jar" lib

AGENT_NATIVE_FILE=$( realpath $( basename $AGENT_NATIVE_FILE ) )

msg "Add the following to Java command line when starting the suite:"
msg "  -agentpath:$AGENT_NATIVE_FILE"

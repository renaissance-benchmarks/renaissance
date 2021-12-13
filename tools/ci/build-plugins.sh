#!/bin/bash
source "$(dirname "$0")/common.sh"

# Build dependencies first
pushd plugins/ubench-agent
./build-ubench-agent.sh

if ! [ -f "lib/ubench-agent.jar" ]; then
    echo "Failed to build lib/ubench-agent.jar, aborting." >&2
    exit 1
fi

popd


# Build the plugins
for plugin_dir in jmx-memory jmx-timers ubench-agent; do
    pushd "plugins/$plugin_dir"
    ci_sbt assembly
    popd
done

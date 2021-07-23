#!/bin/bash
source "$(dirname "$0")/common.sh"

ubench_agent_path="$ROOT_DIR/plugins/ubench-agent/libubench-agent.so"

get_plugin_spec() {
    local plugin_dir="plugins/$1/"
    local plugin_name="$( echo "$1" | tr -d - )"
    local plugin_version="$( sed -n 's#.*version[ ]*:=[ ]*"\([^"]*\)".*#\1#p' <"$plugin_dir/build.sbt" )"
    local plugin_jar="${plugin_dir}target/plugin-${plugin_name}-assembly-$plugin_version.jar"
    echo "${plugin_jar}"
}

java \
    -Xms2500M -Xmx2500M \
    "-agentpath:$ubench_agent_path" \
    -jar "$RENAISSANCE_JAR" \
    --plugin "$( get_plugin_spec "jmx-timers" )" \
    --plugin "$( get_plugin_spec "ubench-agent" )" --with-arg "SYS:wallclock-time,JVM:compilations" \
    -c test \
    -r 2 \
    --csv output.csv \
    --json output.json \
    dummy-empty

echo
echo "Checking output contains expected fields"
echo
collected_metrics="$( jq -r '.data["dummy-empty"]["results"][0]|keys|.[]|.' output.json  | sort )"
echo "$collected_metrics"
echo
for expected in duration_ns jmx_timers_compilation_time_ms jmx_timers_compilation_total_ms ubench_agent_JVM:compilations ubench_agent_SYS:wallclock-time uptime_ns; do
    if ! echo "$collected_metrics" | grep -x -F "$expected"; then
        echo "Metric $expected not found, aborting!" >&2
        exit 1
    fi
done
echo "All is fine!"
echo

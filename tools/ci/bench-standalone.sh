#!/bin/bash
source "$(dirname "$0")/common.sh"

# Test benchmarks under Renaissance harness
java -jar "$RENAISSANCE_JAR" --raw-list > list.txt

unzip "$RENAISSANCE_JAR" -d "extracted-renaissance"

for BENCH in $(cat list.txt); do
	echo "====> $BENCH"
	timeout_with_thread_dump 5m java -Xms2500M -Xmx2500M -jar "./extracted-renaissance/single/$BENCH.jar" -c test -r 1 --csv output.csv --json output.json "$BENCH" || exit 1
done

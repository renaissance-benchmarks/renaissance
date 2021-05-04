#!/bin/bash
source "$(dirname "$0")/common.sh"

# Check that the generated markdown files are up-to-date
java -jar "$RENAISSANCE_JAR" --readme && git diff --exit-code -- :/README.md :/CONTRIBUTION.md

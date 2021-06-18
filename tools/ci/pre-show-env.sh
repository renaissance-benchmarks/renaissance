#!/bin/bash

set -uoe pipefail

set -x

java -version
javac -version
git --version || echo "Git not installed." >&2

cat /etc/os-release || echo "/etc/os-release not found" >&2
uname -a
locale

source "$(dirname "$0")/common.sh"
echo
echo "RENAISSANCE_GIT_VERSION='$RENAISSANCE_GIT_VERSION'"
echo "RENAISSANCE_JAR_NAME='$RENAISSANCE_JAR_NAME'"
echo "RENAISSANCE_JMH_JAR_NAME='$RENAISSANCE_JMH_JAR_NAME'"
echo

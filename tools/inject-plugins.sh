#!/bin/bash
set -euo pipefail

TEMP_DIR="$(mktemp -d)"
BASE_DIR="$(dirname "${0}")"
ROOT_DIR="$(git -C "${BASE_DIR}" rev-parse --show-toplevel)"

function GET_ONE_GLOB_FILE {
    local GLOB="${1}"
    # shellcheck disable=SC2155
    local FILE="$(compgen -G "${GLOB}")"
    if [[ -f "${FILE}" ]]
    then
        echo "${FILE}"
    else
        echo "ERROR: ${GLOB} does not match one file" 1>&2
        exit 8
    fi
}

MAIN_JAR="$(GET_ONE_GLOB_FILE "${ROOT_DIR}/target/renaissance-*.jar")"

# Extract core JAR.
CORE_TEMP_DIR="$(mktemp -d -p "${TEMP_DIR}")"
( cd "${CORE_TEMP_DIR}" ; unzip "${MAIN_JAR}" "unique/renaissance-core/renaissance-core-*.jar" )
CORE_TEMP_JAR="$(GET_ONE_GLOB_FILE "${CORE_TEMP_DIR}/unique/renaissance-core/renaissance-core-*.jar")"

for PLUG_DIR in "${ROOT_DIR}/plugins/"*
do
    PLUG_JAR="$(GET_ONE_GLOB_FILE "${PLUG_DIR}/target/plugin-*.jar")"
    echo "INFO: injecting ${PLUG_JAR}"

    # Extract plugin JAR.
    PLUG_TEMP_DIR="$(mktemp -d -p "${TEMP_DIR}")"
    ( cd "${PLUG_TEMP_DIR}" ; unzip "${PLUG_JAR}" )

    # Update core JAR with plugin JAR content.
    ( cd "${PLUG_TEMP_DIR}" ; zip "${CORE_TEMP_JAR}" . -r --exclude "META-INF/*" )
done

# Update main JAR with core JAR content.
( cd "${CORE_TEMP_DIR}" ; zip "${MAIN_JAR}" "unique/renaissance-core/renaissance-core-*.jar" )

# Clean up.
rm -rf "${TEMP_DIR}"

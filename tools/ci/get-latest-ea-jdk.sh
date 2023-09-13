#!/bin/bash

# Fail the script if any command fails
set -ueo errexit

msg() {
    echo "$( date '+[%Y-%m-%d %H:%M:%S]:' )" "$@" >&2
}

get_latest_version() {
    curl --silent https://jdk.java.net/ \
        | sed -n '/[Ee]arly/s#.*href="\([/0-9]*\)".*#\1#p' \
        | tr -d /
}

get_linux_tarball() {
    curl --silent "https://jdk.java.net/$1/" \
        | sed -n 's#.*href="\(https://download.java.net/.*openjdk.*linux-x64_bin.tar.gz\)".*#\1#p'
}

tarball_name="$1"
mkdir -p "$( dirname "${tarball_name}" )"

latest_version="$( get_latest_version )"
msg "Detected latest early-access JDK to be ${latest_version}"

tarball_url="$( get_linux_tarball "${latest_version}" )"
msg "Will download tarball from ${tarball_url}"

curl --progress-bar "${tarball_url}" -o "${tarball_name}"
msg "Done, stored as ${tarball_name}"

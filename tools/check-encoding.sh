#!/bin/sh

if grep -P -nH -r '--include=*.java' -e '[^\x00-\x7F]' .; then
    exit 1;
fi


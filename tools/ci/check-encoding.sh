#!/bin/bash

# Check Java files for non-ASCII characters, avoiding PCRE
# because 'git grep' on Travis does not understand them.
LC_ALL=C git --no-pager grep -n -e '[^[:cntrl:] -~]' -- ':/*.java'

# Succeed if no match is found, fail otherwise.
[ $? -eq 1 ] && exit 0 || exit 1

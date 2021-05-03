#!/bin/bash

JKS_BASE="$(dirname "$0")/jks"
KEY_STORE="${JKS_BASE}/cacerts"

# Make a copy of the Java trusted CA certificates
cp "$JAVA_HOME/jre/lib/security/cacerts" "$KEY_STORE" || \
	cp "$JAVA_HOME/lib/security/cacerts" "$KEY_STORE"

chmod ug+w "$KEY_STORE"

# Import additional certificates into the trusted CA store
find "${JKS_BASE}/crt" -type f -name '*.pem' | while read PEM_FILE; do
    keytool -importcert -trustcacerts -keystore "$KEY_STORE" -storepass changeit -alias $(basename "$PEM_FILE" .pem) -file "$PEM_FILE" -noprompt
done

#!/bin/sh

# note -- you need to set credentials manually before publishing


function publish() {
	SCALA_VERSION=$1
	sbt "++ $SCALA_VERSION" "reactors-common/publishSigned" "publishSigned"
}

publish 2.10.4
publish 2.11.1

`dirname $0`/publishDocs.sh

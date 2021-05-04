#!/bin/bash

# Fail the script if any command fails
set -o errexit

install_jdk() {
	# Reuse the pre-installed script and mimic Travis behavior.
	# Source the script so that it can update JAVA_HOME and PATH.
	source tools/install-jdk.sh --verbose --workspace "$HOME/.cache/install-jdk" "$@"
}

adoptopenjdk_url() {
	echo "https://api.adoptopenjdk.net/v3/binary/latest/$1/ga/linux/x64/jdk/$2/normal/adoptopenjdk"
}

# Install custom JDK if needed
if [ -n "$USE_JDK" ]; then
	TARGET="$HOME/$USE_JDK"

	if [ "$USE_JDK" = "openj9jdk8" ]; then
		install_jdk --target "$TARGET" \
			--url "$(adoptopenjdk_url 8 openj9)"
	elif [ "$USE_JDK" = "openj9jdk11" ]; then
		install_jdk --target "$TARGET" \
			--url "$(adoptopenjdk_url 11 openj9)"
	else
		echo "Unknown JDK: $USE_JDK!"
		exit 1
	fi
fi


# Dump information about the environment
echo -e "$JAVA_HOME\n"

which java
java -version
echo ""

which javac
javac -version

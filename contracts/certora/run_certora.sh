#!/bin/sh
set -eu

CERTORA_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
LOCAL_JAVA_HOME="$CERTORA_DIR/.tools/java-21/Contents/Home"
LOCAL_KEY_FILE="$CERTORA_DIR/.certora_key"

if [ -z "${CERTORAKEY:-}" ] && [ -r "$LOCAL_KEY_FILE" ]; then
    IFS= read -r CERTORAKEY < "$LOCAL_KEY_FILE"
    export CERTORAKEY
fi

if [ -x "$LOCAL_JAVA_HOME/bin/java" ]; then
    JAVA_HOME="$LOCAL_JAVA_HOME"
    export JAVA_HOME
    PATH="$JAVA_HOME/bin:$PATH"
    export PATH
fi

if ! command -v java >/dev/null 2>&1; then
    echo "Java 21 or later is required; see $CERTORA_DIR/README.md" >&2
    exit 1
fi

if [ ! -x "$CERTORA_DIR/.venv/bin/certoraSorobanProver" ]; then
    echo "Certora CLI is not installed; see $CERTORA_DIR/README.md" >&2
    exit 1
fi

cd "$CERTORA_DIR/confs"
exec "$CERTORA_DIR/.venv/bin/certoraSorobanProver" "$@"

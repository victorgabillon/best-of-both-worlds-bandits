#!/bin/sh
# Repository-relative entry point; no shell expansion of user-supplied commands.
set -eu
SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec python3 "$SCRIPT_DIR/verify.py" "$@"

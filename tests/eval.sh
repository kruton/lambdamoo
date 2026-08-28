#!/usr/bin/env bash
# Evaluate one MOO expression in emergency mode against a disposable database.
set -euo pipefail

DB_FILE="${DB_FILE:-codepoint.db}"
MOO_BIN="${MOO_BIN:-./moo}"

if [ "$#" -eq 0 ]; then
    echo "Usage: $0 MOO expression..." >&2
    exit 1
fi

if [ ! -f "$DB_FILE" ]; then
    echo "Error: Database file '$DB_FILE' not found." >&2
    exit 1
fi

if [ ! -x "$MOO_BIN" ]; then
    echo "Error: MOO binary '$MOO_BIN' not found or not executable." >&2
    exit 1
fi

TMP_DIR=$(mktemp -d /tmp/moo-eval.XXXXXX)
TMP_OUT="$TMP_DIR/output.db"

cleanup() {
    rm -rf "$TMP_DIR"
}
trap cleanup EXIT

printf ';%s\nquit\n' "$*" | "$MOO_BIN" -e "$DB_FILE" "$TMP_OUT"

#!/usr/bin/env bash
# Exercise a small Opal.db object range and report JIT deoptimization reasons.
set -euo pipefail

DB_FILE="${1:-Opal.db}"
MOO_BIN="${2:-./moo}"
FIRST_OBJECT="${3:-0}"
LAST_OBJECT="${4:-25}"

if [ ! -f "$DB_FILE" ]; then
    echo "Error: Database file '$DB_FILE' not found." >&2
    exit 1
fi

if [ ! -x "$MOO_BIN" ]; then
    echo "Error: MOO binary '$MOO_BIN' not found or not executable." >&2
    exit 1
fi

case "$FIRST_OBJECT" in
    '' | *[!0-9]*)
        echo "Error: Object bounds must be non-negative integers." >&2
        exit 1
        ;;
esac

case "$LAST_OBJECT" in
    '' | *[!0-9]*)
        echo "Error: Object bounds must be non-negative integers." >&2
        exit 1
        ;;
esac

if [ "$FIRST_OBJECT" -gt "$LAST_OBJECT" ]; then
    echo "Error: First object must not exceed last object." >&2
    exit 1
fi

TMP_DIR=$(mktemp -d /tmp/opal-jit-deopts.XXXXXX)
TMP_OUT="$TMP_DIR/output.db"
TMP_LOG="$TMP_DIR/server.log"

cleanup() {
    rm -rf "$TMP_DIR"
}
trap cleanup EXIT

python3 - "$MOO_BIN" "$DB_FILE" "$TMP_LOG" "$TMP_OUT" \
    "$FIRST_OBJECT" "$LAST_OBJECT" << 'PYEOF'
import pathlib
import subprocess
import sys

(
    moo_bin,
    db_file,
    log_file,
    output_db,
    first_object,
    last_object,
) = sys.argv[1:]

moo_code = f""";;
for o in [#{first_object}..#{last_object}]
  if (valid(o))
    for v in (verbs(o))
      try
        o:(v)();
      except (ANY)
      endtry
    endfor
  endif
endfor
.
quit
"""

proc = subprocess.run(
    [moo_bin, "-e", "-l", log_file, db_file, output_db],
    input=moo_code,
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
    text=True,
)

if proc.returncode != 0:
    print(f"Error: MOO server exited with status {proc.returncode}.", file=sys.stderr)
    print(proc.stdout, file=sys.stderr)
    print(proc.stderr, file=sys.stderr)
    sys.exit(proc.returncode or 1)

log_lines = pathlib.Path(log_file).read_text(errors="replace").splitlines()
jit_lines = [line.split("JIT:", 1)[1].lstrip() for line in log_lines if "JIT:" in line]

if not jit_lines:
    print("Error: No JIT deoptimization profile was written to server_log().", file=sys.stderr)
    sys.exit(1)

print("=" * 76)
print(
    f"{pathlib.Path(db_file).name} JIT DEOPT REPORT "
    f"(objects #{first_object}..#{last_object})"
)
print("=" * 76)
for line in jit_lines:
    print(line)
print("=" * 76)

if "*Suspended*" in proc.stdout:
    print(
        "Warning: The emergency task suspended; the report covers only verbs "
        "executed before suspension.",
        file=sys.stderr,
    )
PYEOF

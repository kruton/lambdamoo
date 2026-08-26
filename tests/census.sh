#!/usr/bin/env bash
# Automated Opal.db JIT census script
set -euo pipefail

DB_FILE="${1:-Opal.db}"
MOO_BIN="${2:-./moo}"

if [ ! -f "$DB_FILE" ]; then
    echo "Error: Database file '$DB_FILE' not found." >&2
    exit 1
fi

if [ ! -x "$MOO_BIN" ]; then
    echo "Error: MOO binary '$MOO_BIN' not found or not executable." >&2
    exit 1
fi

TMP_DIR=$(mktemp -d /tmp/opal-jit-census.XXXXXX)
TMP_OUT="$TMP_DIR/output.db"
TMP_LOG="$TMP_DIR/output.log"

cleanup() {
    rm -rf "$TMP_DIR"
}
trap cleanup EXIT

python3 - "$MOO_BIN" "$DB_FILE" "$TMP_LOG" "$TMP_OUT" << 'PYEOF'
import re
import subprocess
import sys

moo_bin, db_file, tmp_log, tmp_out = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]

moo_code = """
;;
total = 0;
eligible = 0;
compiled = 0;
reasons = {};
diags = {};
for o in [#0..max_object()]
  if (valid(o))
    for v in [1..length(verbs(o))]
      total = total + 1;
      jit_compile(o, v);
      info = verb_info(o, v, 1);
      if (typeof(info) == LIST && length(info) >= 4 && typeof(info[4]) == LIST)
        meta = info[4];
        r = "unknown";
        d = "unknown";
        for item in (meta)
          if (item[1] == "reason")
            r = item[2];
          elseif (item[1] == "diagnostic")
            d = item[2];
          elseif (item[1] == "state" && item[2] == "compiled")
            compiled = compiled + 1;
          elseif (item[1] == "eligible" && item[2] == 1)
            eligible = eligible + 1;
          endif
        endfor
        r_found = 0;
        for i in [1..length(reasons)]
          if (reasons[i][1] == r)
            reasons[i][2] = reasons[i][2] + 1;
            r_found = 1;
            break;
          endif
        endfor
        if (!r_found)
          reasons = {@reasons, {r, 1}};
        endif
        d_found = 0;
        for i in [1..length(diags)]
          if (diags[i][1] == d)
            diags[i][2] = diags[i][2] + 1;
            d_found = 1;
            break;
          endif
        endfor
        if (!d_found)
          diags = {@diags, {d, 1}};
        endif
      endif
    endfor
  endif
endfor
out = {tostr("TOTAL::", total), tostr("COMPILED::", compiled), tostr("ELIGIBLE::", eligible)};
for item in (reasons)
  out = {@out, tostr("REASON::", item[1], "::", item[2])};
endfor
for item in (diags)
  out = {@out, tostr("DIAG::", item[1], "::", item[2])};
endfor
return out;
.
quit
"""

proc = subprocess.Popen(
    [moo_bin, "-e", "-l", tmp_log, db_file, tmp_out],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
    text=True
)

stdout, stderr = proc.communicate(moo_code)

if proc.returncode != 0:
    print(f"Error: MOO server exited with status {proc.returncode}.", file=sys.stderr)
    print(stderr, file=sys.stderr)
    sys.exit(proc.returncode or 1)

total = 0
eligible = 0
compiled = 0
reasons = []
diags = []

for line in stdout.splitlines():
    if line.startswith('=> {"TOTAL::'):
        items = re.findall(r'"([^"]*)"', line)
        for item in items:
            parts = item.split('::')
            if len(parts) >= 2:
                tag = parts[0]
                if tag == 'TOTAL':
                    total = int(parts[1])
                elif tag == 'COMPILED':
                    compiled = int(parts[1])
                elif tag == 'ELIGIBLE':
                    eligible = int(parts[1])
                elif tag == 'REASON' and len(parts) >= 3:
                    reasons.append((parts[1], int(parts[2])))
                elif tag == 'DIAG' and len(parts) >= 3:
                    diags.append((parts[1], int(parts[2])))
        break

if total == 0:
    print("Error: Failed to obtain census output from MOO server.", file=sys.stderr)
    print(stdout, file=sys.stderr)
    print(stderr, file=sys.stderr)
    sys.exit(1)

reasons.sort(key=lambda x: x[1], reverse=True)
diags.sort(key=lambda x: x[1], reverse=True)
normalized_diags = {}
for diagnostic, count in diags:
    normalized = re.sub(r"^anchor: pc [0-9]+ ", "anchor: pc * ", diagnostic)
    normalized_diags[normalized] = normalized_diags.get(normalized, 0) + count
normalized_diags = sorted(normalized_diags.items(), key=lambda x: x[1], reverse=True)

print("=" * 76)
print("OPAL.DB JIT CENSUS REPORT")
print("=" * 76)
print(f"Total Verbs    : {total}")
print(f"Compiled (JIT) : {compiled} ({compiled/total*100:.2f}%)")
print(f"Eligible (JIT) : {eligible} ({eligible/total*100:.2f}%)")
print(f"Unsupported    : {total - eligible} ({(total - eligible)/total*100:.2f}%)")

print("\n" + "-" * 76)
print(f"{'TOP-LEVEL REASON CATEGORY':<40} {'COUNT':>10} {'PERCENT':>18}")
print("-" * 76)
for r, count in reasons:
    print(f"{r:<40} {count:>10} {count/total*100:>17.2f}%")

print("\n" + "-" * 76)
print(f"{'DETAILED DIAGNOSTIC (TOP 40)':<52} {'COUNT':>8} {'PERCENT':>12}")
print("-" * 76)
for d, count in diags[:40]:
    print(f"{d:<52} {count:>8} {count/total*100:>11.2f}%")

print("\n" + "-" * 76)
print(f"{'NORMALIZED DIAGNOSTIC (TOP 40)':<52} {'COUNT':>8} {'PERCENT':>12}")
print("-" * 76)
for d, count in normalized_diags[:40]:
    print(f"{d:<52} {count:>8} {count/total*100:>11.2f}%")

print("=" * 76)
PYEOF

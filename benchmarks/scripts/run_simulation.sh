#!/usr/bin/env bash
# run_simulation.sh <circuit> <work_dir> <testbench_dir>
# Runs ngspice on testbench → metrics.json
set -euo pipefail

CIRCUIT="$1"
WORK_DIR="$2"
TESTBENCH_DIR="$3"
TB_SRC="${TESTBENCH_DIR}/${CIRCUIT}/tb.sp"

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

if [ ! -f "$TB_SRC" ]; then
  echo "[run_simulation] ERROR: testbench not found: ${TB_SRC}" >&2
  exit 1
fi

if [ ! -f "${WORK_DIR}/extracted.spice" ]; then
  echo "[run_simulation] ERROR: extracted.spice not found — run extraction first" >&2
  exit 1
fi

echo "[run_simulation] Running ngspice for ${CIRCUIT} ..."

# ALIGN names the top-level GDS cell with an uppercase suffix (e.g. BUFFER_0).
# Rename it to $CIRCUIT so the testbench .include + instantiation matches.
python3 - <<'PYEOF'
import re, os, sys
work_dir = os.environ['WORK_DIR']
circuit  = os.environ['CIRCUIT']
path = os.path.join(work_dir, 'extracted.spice')
content = open(path).read()
subckts = re.findall(r'^\.subckt\s+(\S+)', content, re.MULTILINE | re.IGNORECASE)
if subckts:
    topcell = subckts[-1]
    if topcell.lower() != circuit.lower():
        content = re.sub(rf'^(\.subckt\s+){re.escape(topcell)}(\b)',
                         rf'\g<1>{circuit}\2', content,
                         flags=re.MULTILINE | re.IGNORECASE)
        content = re.sub(rf'^(\.ends\s+){re.escape(topcell)}(\b)',
                         rf'\g<1>{circuit}\2', content,
                         flags=re.MULTILINE | re.IGNORECASE)
        open(path, 'w').write(content)
        print(f'[run_simulation] renamed subckt {topcell!r} → {circuit!r}')
PYEOF

cp "$TB_SRC" "${WORK_DIR}/tb.sp"

NGSPICE_OUT="${WORK_DIR}/ngspice_out.txt"

# Run from WORK_DIR so .include extracted.spice resolves correctly
( cd "${WORK_DIR}" && ngspice -b tb.sp 2>&1 ) | tee "$NGSPICE_OUT" || true

echo "[run_simulation] ngspice done."

python3 "${SCRIPT_DIR}/parse_sim_metrics.py" \
  "$CIRCUIT" "$WORK_DIR" "$NGSPICE_OUT"

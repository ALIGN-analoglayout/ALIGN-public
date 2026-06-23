#!/usr/bin/env bash
# run_simulation.sh <circuit> <work_dir> <testbench_dir> [schematic_sp]
# Runs ngspice on testbench → metrics.json
#
# If extracted.spice (from Magic) has no .subckt definition (common for
# mock PDKs with metal-only layers), <schematic_sp> is prepended so the
# testbench can instantiate the circuit using schematic-level transistors.
set -euo pipefail

CIRCUIT="$1"
WORK_DIR="$2"
TESTBENCH_DIR="$3"
SCHEMATIC_SP="${4:-}"
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

# If extracted.spice lacks a .subckt (metal-only PDK — only RC parasitics),
# prepend the schematic .sp so the testbench can instantiate the circuit.
python3 - "${WORK_DIR}/extracted.spice" "${CIRCUIT}" "${SCHEMATIC_SP}" <<'PYEOF'
import re, sys
path, circuit, schematic_sp = sys.argv[1], sys.argv[2], sys.argv[3]
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
        print(f'[run_simulation] renamed subckt {topcell!r} -> {circuit!r}')
    else:
        print(f'[run_simulation] subckt already named {circuit!r}, no rename needed')
elif schematic_sp:
    import pathlib
    sp = pathlib.Path(schematic_sp)
    if sp.exists():
        schematic = sp.read_text()
        # Strip FinFET-specific MOSFET instance parameters that ngspice rejects.
        # These are layout hints (nfin=fins, nf=fingers, stack, parallel) that
        # don't map to standard SPICE MOSFET parameters.
        for param in ('nfin', 'nf', 'stack', 'parallel'):
            schematic = re.sub(rf'\s+{param}=\S+', '', schematic)
        # Prepend schematic; parasitics in extracted.spice remain as RC overlay
        open(path, 'w').write(schematic + '\n' + content)
        print(f'[run_simulation] no subckt in extracted.spice — prepended schematic {schematic_sp}')
    else:
        print(f'[run_simulation] WARNING: schematic not found: {schematic_sp}')
else:
    print(f'[run_simulation] WARNING: no .subckt in extracted.spice and no schematic provided')
PYEOF

cp "$TB_SRC" "${WORK_DIR}/tb.sp"

NGSPICE_OUT="${WORK_DIR}/ngspice_out.txt"

# Run from WORK_DIR so .include extracted.spice resolves correctly
( cd "${WORK_DIR}" && ngspice -b tb.sp 2>&1 ) | tee "$NGSPICE_OUT" || true

echo "[run_simulation] ngspice done."

python3 "${SCRIPT_DIR}/parse_sim_metrics.py" \
  "$CIRCUIT" "$WORK_DIR" "$NGSPICE_OUT"

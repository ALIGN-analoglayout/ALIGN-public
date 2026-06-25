#!/usr/bin/env bash
# run_simulation.sh <circuit> <work_dir> <testbench_dir> [schematic_sp] [sky130_models]
# Runs ngspice on testbench → metrics.json
#
# If extracted.spice (from Magic) has no .subckt definition (common for
# mock PDKs with metal-only layers), <schematic_sp> is prepended so the
# testbench can instantiate the circuit using schematic-level transistors.
#
# If <sky130_models> is provided and points to a sky130 ngspice library file
# (e.g. from volare), the testbench's MODELS_BEGIN/END stub block is replaced
# with a real sky130 BSIM4 .lib include and ALIGN device names are mapped to
# their canonical sky130_fd_pr__ equivalents.
set -euo pipefail

CIRCUIT="$1"
WORK_DIR="$2"
TESTBENCH_DIR="$3"
SCHEMATIC_SP="${4:-}"
SKY130_MODELS="${5:-}"
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

# Determine whether real sky130 BSIM4 models are available.
# With real models: nf is a valid BSIM4 instance parameter and must not be
# stripped. With level-1 stubs: nf is unrecognised and must be stripped.
if [ -n "$SKY130_MODELS" ] && [ -f "$SKY130_MODELS" ]; then
  REAL_BSIM4="true"
else
  REAL_BSIM4="false"
fi

# If extracted.spice lacks a .subckt (metal-only PDK — only RC parasitics),
# prepend the schematic .sp so the testbench can instantiate the circuit.
python3 - "${WORK_DIR}/extracted.spice" "${CIRCUIT}" "${SCHEMATIC_SP}" "${REAL_BSIM4}" <<'PYEOF'
import re, sys

path, circuit, schematic_sp, real_bsim4 = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]

# Map ALIGN convenience device names to canonical sky130_fd_pr__ names.
# Used when real BSIM4 models are available so every instance references a
# device that the real PDK model file actually defines.
ALIGN_TO_SKY130 = {
    'nmos_rvt':  'sky130_fd_pr__nfet_01v8',
    'pmos_rvt':  'sky130_fd_pr__pfet_01v8',
    'nmos_lvt':  'sky130_fd_pr__nfet_01v8__lvt',
    'pmos_lvt':  'sky130_fd_pr__pfet_01v8__lvt',
    'nmos_hvt':  'sky130_fd_pr__nfet_01v8__hvt',
    'pmos_hvt':  'sky130_fd_pr__pfet_01v8__hvt',
}

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
        if real_bsim4 == 'true':
            # Real BSIM4: keep nf (valid parameter), strip only FinFET/ALIGN-layout hints.
            # Also map ALIGN device names to canonical sky130_fd_pr__ names so every
            # instance matches a model defined in the real PDK library file.
            strip_params = ('nfin', 'stack', 'parallel')
            for align_name, sky130_name in ALIGN_TO_SKY130.items():
                schematic = re.sub(rf'\b{re.escape(align_name)}\b', sky130_name, schematic)
            print('[run_simulation] mapped ALIGN device names to sky130_fd_pr__ equivalents')
        else:
            # Level-1 stub models: nf is unrecognised — strip all non-standard params.
            strip_params = ('nfin', 'nf', 'stack', 'parallel')
        for param in strip_params:
            schematic = re.sub(rf'\s+{param}=\S+', '', schematic)
        # Replace extracted.spice with just the schematic subckt.
        # The RC-only extracted.spice from mock PDKs contains ".option scale=1n"
        # which rescales device widths/lengths to attometer range, causing DC OP
        # failure before AC analysis even starts. Metal RC parasitics are
        # meaningless without real transistor physics anyway.
        open(path, 'w').write(schematic + '\n')
        print(f'[run_simulation] replaced extracted.spice with schematic {schematic_sp}')
    else:
        print(f'[run_simulation] WARNING: schematic not found: {schematic_sp}')
else:
    print(f'[run_simulation] WARNING: no .subckt in extracted.spice and no schematic provided')
PYEOF

cp "$TB_SRC" "${WORK_DIR}/tb.sp"

# If real sky130 BSIM4 models are available, replace the stub MODELS_BEGIN/END
# block in the testbench with a .lib include of the real PDK model file.
if [ "$REAL_BSIM4" = "true" ]; then
  python3 - "${WORK_DIR}/tb.sp" "$SKY130_MODELS" <<'PYEOF'
import re, sys
tb_path, models_path = sys.argv[1], sys.argv[2]
content = open(tb_path).read()
replacement = f'.lib {models_path} tt'
content_new = re.sub(
    r'(\* MODELS_BEGIN[^\n]*\n).*?(\n\* MODELS_END)',
    rf'\1{replacement}\2',
    content,
    flags=re.DOTALL
)
if content_new != content:
    open(tb_path, 'w').write(content_new)
    print(f'[run_simulation] substituted real sky130 BSIM4 models: {models_path}')
else:
    print('[run_simulation] WARNING: MODELS_BEGIN/END not found; stub models will be used')
PYEOF
fi

NGSPICE_OUT="${WORK_DIR}/ngspice_out.txt"

# Run from WORK_DIR so .include extracted.spice resolves correctly
( cd "${WORK_DIR}" && ngspice -b tb.sp 2>&1 ) | tee "$NGSPICE_OUT" || true

echo "[run_simulation] ngspice done."

python3 "${SCRIPT_DIR}/parse_sim_metrics.py" \
  "$CIRCUIT" "$WORK_DIR" "$NGSPICE_OUT"

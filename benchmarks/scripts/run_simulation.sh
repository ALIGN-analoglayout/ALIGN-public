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
    # LVT nfet: sky130 uses single underscore before the variant suffix.
    # LVT pfet (pfet_01v8_lvt) is only characterised for L >= 0.35µm; ALIGN
    # uses L=0.15µm so that model has no valid bin.  Fall back to standard
    # pfet_01v8 (characterised down to L=0.15µm) as a simulation proxy.
    'nmos_lvt':  'sky130_fd_pr__nfet_01v8_lvt',
    'pmos_lvt':  'sky130_fd_pr__pfet_01v8',
    # HVT: sky130 has no NFET HVT device; fall back to standard threshold.
    # PFET HVT exists and uses single underscore before the variant suffix.
    'nmos_hvt':  'sky130_fd_pr__nfet_01v8',
    'pmos_hvt':  'sky130_fd_pr__pfet_01v8_hvt',
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
            # Map ALIGN device names to canonical sky130_fd_pr__ names.
            strip_params = ('nfin', 'stack', 'parallel')
            for align_name, sky130_name in ALIGN_TO_SKY130.items():
                schematic = re.sub(rf'\b{re.escape(align_name)}\b', sky130_name, schematic)
            print('[run_simulation] mapped ALIGN device names to sky130_fd_pr__ equivalents')
            # sky130 PDK defines all transistors as .subckt wrappers, NOT as .model
            # entries.  SPICE M devices look for .model; X devices use .subckt.
            # Convert every "M<name> ... sky130_fd_pr__..." line to "X<name> ...".
            schematic = re.sub(
                r'^(\s*)[mM](\S+)((?:\s+\S+){4}\s+sky130_fd_pr__)',
                r'\1x\2\3',
                schematic,
                flags=re.MULTILINE
            )
            print('[run_simulation] converted M to X instances for sky130_fd_pr__ subcircuits')
            # sky130 models_tt.spice sets .option scale=1.0u, so ngspice expects
            # device W/L in µm. ALIGN generates W/L in meters. Additionally,
            # nf (finger count) must be folded into total W because BSIM4 binning
            # selects per-finger models, and narrow-W bins have unphysical negative u0
            # when evaluated at L=150nm — folding nf into total W selects a wide-W
            # bin (model.8) that has valid u0 for our devices.
            # Also fold m (instance multiplier) into W when present.
            def _convert_sky130_dims(line):
                if 'sky130_fd_pr__' not in line:
                    return line
                if re.match(r'\s*[\*\.]', line):
                    return line
                def _gp(name):
                    m = re.search(rf'(?<![a-zA-Z_]){re.escape(name)}\s*=\s*([\d.e+-]+)', line, re.IGNORECASE)
                    return float(m.group(1)) if m else None
                l_m = _gp('l')
                w_m = _gp('w')
                if l_m is None or w_m is None:
                    return line
                nf_v = _gp('nf') or 1.0
                m_v  = _gp('m')  or 1.0
                l_um = l_m * 1e6
                w_um = w_m * nf_v * m_v * 1e6
                r = re.sub(r'(?<![a-zA-Z_])l\s*=\s*[\d.e+-]+', '', line,   flags=re.IGNORECASE)
                r = re.sub(r'(?<![a-zA-Z_])w\s*=\s*[\d.e+-]+', '', r,      flags=re.IGNORECASE)
                r = re.sub(r'(?<![a-zA-Z_])nf\s*=\s*[\d.e+-]+', '', r,     flags=re.IGNORECASE)
                r = re.sub(r'(?<![a-zA-Z_])m\s*=\s*[\d.e+-]+', '', r,      flags=re.IGNORECASE)
                return r.rstrip() + f' l={l_um:.6g} w={w_um:.6g}\n'
            schematic = ''.join(_convert_sky130_dims(ln) for ln in schematic.splitlines(keepends=True))
            print('[run_simulation] converted sky130 L/W from meters to µm, folded nf+m into total W')
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

# If real sky130 BSIM4 models are available, flatten the sky130 .lib file's
# tt section (resolving all nested .lib references with absolute paths) into a
# single models_tt.spice in WORK_DIR.  Using a flat .include avoids ngspice's
# nested-lib relative-path resolution bugs seen with some Ubuntu builds.
if [ "$REAL_BSIM4" = "true" ]; then
  python3 - "${WORK_DIR}/tb.sp" "${WORK_DIR}/models_tt.spice" "$SKY130_MODELS" <<'PYEOF'
import os, re, sys

tb_path, flat_path, models_path = sys.argv[1], sys.argv[2], sys.argv[3]

def expand_file(file_path, depth=0):
    """Inline a file, recursively resolving .include statements."""
    if depth > 12:
        return f'* max depth reached: {file_path}\n'
    fdir = os.path.dirname(os.path.realpath(file_path))
    try:
        content = open(file_path).read()
    except OSError:
        return f'* missing file: {file_path}\n'

    def inline_include(m):
        rel = m.group(1) or m.group(2)
        return expand_file(os.path.normpath(os.path.join(fdir, rel)), depth + 1)

    return re.sub(
        r"\.include\s+(?:'([^']+)'|\"([^\"]+)\")",
        inline_include, content, flags=re.IGNORECASE
    )

def flatten_lib(lib_path, section, depth=0):
    """Flatten a named .lib/.endl section; all nested .lib and .include refs
    are recursively resolved using each file's own directory as base."""
    if depth > 12:
        return f'* max depth reached: {lib_path}\n'
    fdir = os.path.dirname(os.path.realpath(lib_path))
    try:
        raw = open(lib_path).read()
    except OSError:
        return f'* missing file: {lib_path}\n'

    # sky130.lib.spice has multiple .lib tt ... .endl tt blocks (one per device
    # family: standard, LVT, HVT, etc.).  re.search only finds the first block,
    # leaving LVT/HVT subckt definitions out of the flattened file.  Use
    # finditer to concatenate every block for the requested section.
    bodies = [m.group(1) for m in re.finditer(
        r'\.lib\s+' + re.escape(section) + r'\b(.*?)\.endl(?:\s+' + re.escape(section) + r'\b)?',
        raw, re.DOTALL | re.IGNORECASE
    )]
    body = '\n'.join(bodies) if bodies else raw

    # Expand nested .lib 'relpath' corner references
    def expand_lib(nm):
        rel = nm.group(1) or nm.group(2)
        corner = (nm.group(3) or section).strip()
        return flatten_lib(os.path.normpath(os.path.join(fdir, rel)), corner, depth + 1)

    body = re.sub(
        r"\.lib\s+(?:'([^']+)'|\"([^\"]+)\")\s+(\w+)",
        expand_lib, body, flags=re.IGNORECASE
    )

    # Expand .include 'relpath' references (sky130.lib.spice may use these)
    def expand_include(nm):
        rel = nm.group(1) or nm.group(2)
        return expand_file(os.path.normpath(os.path.join(fdir, rel)), depth + 1)

    body = re.sub(
        r"\.include\s+(?:'([^']+)'|\"([^\"]+)\")",
        expand_include, body, flags=re.IGNORECASE
    )

    return body

flat_content = flatten_lib(models_path, 'tt')
open(flat_path, 'w').write(flat_content)
print(f'[run_simulation] flattened sky130 BSIM4 tt models -> {flat_path}')

# Splice the flat include into the testbench
content = open(tb_path).read()
replacement = '.include models_tt.spice'
content_new = re.sub(
    r'(\* MODELS_BEGIN[^\n]*\n).*?(\n\* MODELS_END)',
    rf'\1{replacement}\2',
    content,
    flags=re.DOTALL
)
if content_new != content:
    open(tb_path, 'w').write(content_new)
    print(f'[run_simulation] testbench now uses flat model include')
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

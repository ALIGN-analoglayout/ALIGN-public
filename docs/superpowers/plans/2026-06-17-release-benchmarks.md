# Release Benchmark Metrics System — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Automatically collect layout quality and post-layout simulation metrics after every PyPI release of `align-analoglayout` and publish a trend dashboard to GitHub Pages.

**Architecture:** A `benchmark.yml` GitHub Actions workflow triggers via `workflow_run` after the publish workflow succeeds. Each of 6 representative circuits runs as a parallel matrix job: ALIGN → Magic extraction → ngspice simulation → metrics JSON. An aggregate job merges results, detects regressions, and publishes a Chart.js static dashboard to the `gh-pages` branch.

**Tech Stack:** GitHub Actions, Magic VLSI 7.3.x (built from source, cached), ngspice 43 (apt), Python 3.10, Chart.js 4.4.0 (CDN), align-analoglayout (from PyPI)

**Spec:** `docs/superpowers/specs/2026-06-17-release-benchmarks-design.md`

---

## File Map

```
benchmarks/
  config.json                                  ← tool versions, circuit list, thresholds
  magic_tech/
    FinFET14nm_Mock_PDK/
      FinFET14nm.tech                          ← Magic layer + RC definitions
      FinFET14nm.magicrc                       ← Magic startup (references .tech)
      ext2spice.tcl                            ← extraction TCL script
  testbenches/
    buffer/tb.sp
    five_transistor_ota/tb.sp
    current_mirror_ota/tb.sp
    high_speed_comparator/tb.sp
    variable_gain_amplifier/tb.sp
    switched_capacitor_filter/tb.sp
  scripts/
    run_align.sh          ← run ALIGN, extract LEF area + runtime, convert GDS
    run_extraction.sh     ← Magic GDS → extracted.spice
    run_simulation.sh     ← ngspice testbench → metrics JSON
    aggregate.py          ← merge per-circuit JSONs, update history.json, detect regressions
    render_dashboard.py   ← generate index.html from history.json

.github/workflows/
  benchmark.yml           ← full CI workflow
```

---

## Task 1: Scaffold and config

**Files:**
- Create: `benchmarks/config.json`
- Create: `benchmarks/magic_tech/FinFET14nm_Mock_PDK/.gitkeep`
- Create: `benchmarks/testbenches/.gitkeep`
- Create: `benchmarks/scripts/.gitkeep`

- [ ] **Step 1: Create directory structure and config**

```bash
mkdir -p benchmarks/magic_tech/FinFET14nm_Mock_PDK
mkdir -p benchmarks/testbenches/buffer
mkdir -p benchmarks/testbenches/five_transistor_ota
mkdir -p benchmarks/testbenches/current_mirror_ota
mkdir -p benchmarks/testbenches/high_speed_comparator
mkdir -p benchmarks/testbenches/variable_gain_amplifier
mkdir -p benchmarks/testbenches/switched_capacitor_filter
mkdir -p benchmarks/scripts
```

Write `benchmarks/config.json`:

```json
{
  "magic_version": "7.3.456",
  "ngspice_version": "43",
  "pdk": "FinFET14nm_Mock_PDK",
  "circuits": [
    "buffer",
    "five_transistor_ota",
    "current_mirror_ota",
    "high_speed_comparator",
    "variable_gain_amplifier",
    "switched_capacitor_filter"
  ],
  "regression_thresholds": {
    "warning_pct": 10,
    "failure_pct": 25
  }
}
```

- [ ] **Step 2: Commit scaffold**

```bash
git add benchmarks/
git commit -m "chore: scaffold benchmarks directory structure"
```

---

## Task 2: Magic tech files for FinFET14nm_Mock_PDK

**Background:** The GDS layer numbers come from `pdks/FinFET14nm_Mock_PDK/layers.json`:
- M1: GDS 13/0, M2: GDS 15/0, M3: GDS 19/20, M4: GDS 21/0, M5: GDS 23/0
- V0: GDS 12/0, V1: GDS 14/0, V2: GDS 16/20, V3: GDS 17/0, V4: GDS 22/0

**Files:**
- Create: `benchmarks/magic_tech/FinFET14nm_Mock_PDK/FinFET14nm.tech`
- Create: `benchmarks/magic_tech/FinFET14nm_Mock_PDK/FinFET14nm.magicrc`
- Create: `benchmarks/magic_tech/FinFET14nm_Mock_PDK/ext2spice.tcl`

- [ ] **Step 1: Write the Magic tech file**

Create `benchmarks/magic_tech/FinFET14nm_Mock_PDK/FinFET14nm.tech`:

```
tech
  format 31
  FinFET14nm_Mock
end

planes
  active,a
  metal1,m1
  metal2,m2
  metal3,m3
  metal4,m4
  metal5,m5
  via01,v01
  via12,v12
  via23,v23
  via34,v34
  via45,v45
end

types
  active    ndiff,pdiff
  metal1    m1
  metal2    m2
  metal3    m3
  metal4    m4
  metal5    m5
  via01     via01
  via12     via12,via1
  via23     via23,via2
  via34     via34,via3
  via45     via45,via4
end

contact
  via01   via01   m1   m2
  via12   via12   m2   m3
  via23   via23   m3   m4
  via34   via34   m4   m5
end

styles
  styletype mos
  m1  blue
  m2  green
  m3  red
  m4  cyan
  m5  magenta
  via01  white
  via12  white
  via23  white
  via34  white
end

cifoutput
  style gds2
  scalefactor 1000 calmaunit 1
  layer 13 m1
  layer 15 m2
  layer 19 m3
  layer 21 m4
  layer 23 m5
  layer 12 via01
  layer 14 via12
  layer 16 via23
  layer 17 via34
  layer 22 via45
end

cifinput
  style gds2
  scalefactor 1000 calmaunit 1
  layer m1    13 0
  layer m2    15 0
  layer m3    19 20
  layer m4    21 0
  layer m5    23 0
  layer via01 12 0
  layer via12 14 0
  layer via23 16 20
  layer via34 17 0
  layer via45 22 0
end

extract
  style default
  resist m1   0.12
  resist m2   0.10
  resist m3   0.08
  resist m4   0.08
  resist m5   0.08
  contact via01 5
  contact via12 5
  contact via23 5
  contact via34 5
  contact via45 5
  areacap m1   35
  areacap m2   28
  areacap m3   22
  areacap m4   22
  areacap m5   22
end
```

- [ ] **Step 2: Write the .magicrc startup file**

Create `benchmarks/magic_tech/FinFET14nm_Mock_PDK/FinFET14nm.magicrc`:

```
tech load FinFET14nm.tech
set SUB_RULES 0
```

- [ ] **Step 3: Write the extraction TCL script**

Create `benchmarks/magic_tech/FinFET14nm_Mock_PDK/ext2spice.tcl`:

```tcl
# ext2spice.tcl — reads INPUT_GDS, extracts parasitics, writes SPICE
# Usage: magic -dnull -noconsole -rcfile FinFET14nm.magicrc < ext2spice.tcl
# Environment variables set before invocation:
#   INPUT_GDS  — absolute path to GDS file
#   OUTPUT_DIR — directory to write extracted.spice

set input_gds $env(INPUT_GDS)
set output_dir $env(OUTPUT_DIR)

gds readonly true
gds rescale false
gds read $input_gds

# Get top cell (last in the list is the top-level)
set cells [cellname list allcells]
set topcell [lindex $cells end]

load $topcell
select top cell

# Run extraction
extract all

# Write extracted SPICE
ext2spice rthresh 0
ext2spice cthresh 0
ext2spice format ngspice
ext2spice -o ${output_dir}/extracted.spice

# Clean up .ext files
foreach f [glob -nocomplain *.ext] { file delete $f }

quit
```

- [ ] **Step 4: Commit Magic tech files**

```bash
git add benchmarks/magic_tech/
git commit -m "feat: add Magic tech files for FinFET14nm_Mock_PDK"
```

---

## Task 3: Testbench netlists (6 circuits)

**Note:** These use `FinFET14nm_Mock_PDK/models.sp` which has level-1 MOSFET models with VTO=0. Simulations converge but numbers are not physically accurate — they are consistent across releases, which is what matters for regression tracking.

**Files:**
- Create: `benchmarks/testbenches/buffer/tb.sp`
- Create: `benchmarks/testbenches/five_transistor_ota/tb.sp`
- Create: `benchmarks/testbenches/current_mirror_ota/tb.sp`
- Create: `benchmarks/testbenches/high_speed_comparator/tb.sp`
- Create: `benchmarks/testbenches/variable_gain_amplifier/tb.sp`
- Create: `benchmarks/testbenches/switched_capacitor_filter/tb.sp`

- [ ] **Step 1: Write buffer testbench**

Ports: `vin vout vdd vss`. Measures propagation delay.

Create `benchmarks/testbenches/buffer/tb.sp`:

```spice
* Buffer post-layout testbench
* Measures: tpHL (ns), tpLH (ns)
.option TNOM=27 GMIN=1e-12

.include ../../../../pdks/FinFET14nm_Mock_PDK/models.sp
.include ../../extracted.spice

xdut vin vout vdd vss buffer
vdd vdd 0 dc 1.0
vss vss 0 dc 0
vin vin 0 pulse(0 1.0 0 10p 10p 500p 1n)

.tran 1p 2n

.measure tran tphl_ns
+ trig v(vin)  val=0.5 rise=1
+ targ v(vout) val=0.5 fall=1
+ td=1e-12

.measure tran tplh_ns
+ trig v(vin)  val=0.5 fall=1
+ targ v(vout) val=0.5 rise=1
+ td=1e-12

.end
```

- [ ] **Step 2: Write five_transistor_ota testbench**

Ports: `vbias vss vdd von vin vip`. Measures DC gain, UGBW.

Create `benchmarks/testbenches/five_transistor_ota/tb.sp`:

```spice
* 5-transistor OTA post-layout testbench
* Measures: gain_db, ugbw_mhz, phase_margin_deg
.option TNOM=27 GMIN=1e-12

.include ../../../../pdks/FinFET14nm_Mock_PDK/models.sp
.include ../../extracted.spice

xdut vbias vss vdd von vin vip five_transistor_ota
vdd vdd 0 dc 1.0
vss vss 0 dc 0
vbias vbias 0 dc 0.4
* differential AC stimulus: vin=+0.5V+ac, vip=+0.5V (common mode 0.5V)
vin vin 0 dc 0.5 ac 0.5
vip vip 0 dc 0.5 ac -0.5

.ac dec 100 1k 10g

.measure ac gain_db   max vdb(von)
.measure ac ugbw_mhz  when vdb(von)=0 cross=last td=1k
+ goal=1e6
.measure ac pm_freq   when vdb(von)=0 cross=last td=1k
.measure ac phase_at_ugbw find vp(von) at=pm_freq

.end
```

- [ ] **Step 3: Write current_mirror_ota testbench**

Ports: `id vinn vinp vss vdd voutp vbiasnd`. Measures DC gain, bandwidth.

Create `benchmarks/testbenches/current_mirror_ota/tb.sp`:

```spice
* Current mirror OTA post-layout testbench
* Measures: gain_db, bandwidth_mhz
.option TNOM=27 GMIN=1e-12

.include ../../../../pdks/FinFET14nm_Mock_PDK/models.sp
.include ../../extracted.spice

xdut id vinn vinp vss vdd voutp vbiasnd current_mirror_ota
vdd vdd 0 dc 1.0
vss vss 0 dc 0
vid id 0 dc 0.4
vbiasnd vbiasnd 0 dc 0.3
vinn vinn 0 dc 0.5 ac -0.5
vinp vinp 0 dc 0.5 ac  0.5

.ac dec 100 1k 10g

.measure ac gain_db      max vdb(voutp)
.measure ac bandwidth_mhz when vdb(voutp)=gain_db-3 fall=last
+ goal=1e6

.end
```

- [ ] **Step 4: Write high_speed_comparator testbench**

Ports: `clk vcc vin vip von vop vss`. Measures static power.

Create `benchmarks/testbenches/high_speed_comparator/tb.sp`:

```spice
* High-speed comparator post-layout testbench
* Measures: static_power_uw, regen_time_ns
.option TNOM=27 GMIN=1e-12

.include ../../../../pdks/FinFET14nm_Mock_PDK/models.sp
.include ../../extracted.spice

xdut clk vcc vin vip von vop vss high_speed_comparator
vcc vcc 0 dc 1.0
vss vss 0 dc 0
* clk low (evaluate phase), small differential input
vclk clk 0 pulse(1.0 0 0 10p 10p 500p 1n)
vin vin  0 dc 0.45
vip vip  0 dc 0.55

.tran 1p 2n

* Static power = supply current × VCC during clk-low phase
.measure tran iavg_a avg i(vcc) from=0.2n to=0.4n
.measure tran static_power_uw param='iavg_a * 1.0 * 1e6'

* Regeneration: time for vop-von to cross from 0.1 to 0.9
.measure tran regen_time_ns
+ trig v(vop) val=0.1 rise=1
+ targ v(vop) val=0.9 rise=1
+ td=1e-12 goal=1e-9

.end
```

- [ ] **Step 5: Write variable_gain_amplifier testbench**

Ports: `vmirror_vga s0 s1 s2 s3 vin1 vin2 vout_vga1 vout_vga2 vps vgnd`. Measures gain at max-gain setting.

Create `benchmarks/testbenches/variable_gain_amplifier/tb.sp`:

```spice
* Variable gain amplifier post-layout testbench
* Measures: gain_db (at max gain: s0=1 s1=0 s2=0 s3=0), bandwidth_mhz
.option TNOM=27 GMIN=1e-12

.include ../../../../pdks/FinFET14nm_Mock_PDK/models.sp
.include ../../extracted.spice

xdut vmirror_vga s0 s1 s2 s3 vin1 vin2 vout_vga1 vout_vga2 vps vgnd variable_gain_amplifier
vps   vps  0 dc 1.0
vgnd  vgnd 0 dc 0
vmirror vmirror_vga 0 dc 0.4
* max gain: s0 high, others low
vs0  s0  0 dc 1.0
vs1  s1  0 dc 0
vs2  s2  0 dc 0
vs3  s3  0 dc 0
vin1 vin1 0 dc 0.5 ac  0.5
vin2 vin2 0 dc 0.5 ac -0.5

.ac dec 100 1k 10g

.measure ac gain_db       max vdb(vout_vga1)
.measure ac bandwidth_mhz when vdb(vout_vga1)=gain_db-3 fall=last
+ goal=1e6

.end
```

- [ ] **Step 6: Write switched_capacitor_filter testbench**

Ports: `voutn voutp vinp vinn id agnd vss vdd`. Measures -3dB frequency.

Create `benchmarks/testbenches/switched_capacitor_filter/tb.sp`:

```spice
* Switched capacitor filter post-layout testbench
* Measures: f3db_mhz, passband_ripple_db
* Note: SC filter uses clock - run as continuous-time approximation for AC analysis
.option TNOM=27 GMIN=1e-12

.include ../../../../pdks/FinFET14nm_Mock_PDK/models.sp
.include ../../extracted.spice

xdut voutn voutp vinp vinn id agnd vss vdd switched_capacitor_filter
vdd  vdd  0 dc 1.0
vss  vss  0 dc 0
vagnd agnd 0 dc 0.5
vid  id   0 dc 0.4
vinp vinp 0 dc 0.5 ac  0.5
vinn vinn 0 dc 0.5 ac -0.5

.ac dec 100 1k 10g

.measure ac gain_max      max vdb(voutp)
.measure ac f3db_mhz      when vdb(voutp)=gain_max-3 fall=last
+ goal=1e6
.measure ac passband_ripple_db param='gain_max - vdb(voutp) at=1e3'

.end
```

- [ ] **Step 7: Commit all testbenches**

```bash
git add benchmarks/testbenches/
git commit -m "feat: add ngspice testbenches for 6 benchmark circuits"
```

---

## Task 4: run_align.sh — run ALIGN and extract layout metrics

**What it does:** Runs ALIGN on a circuit, measures wall-clock runtime, parses area from the output LEF, and counts vias and wirelength from GDS geometry. Outputs `layout_metrics.json`.

**Files:**
- Create: `benchmarks/scripts/run_align.sh`
- Create: `benchmarks/scripts/parse_layout_metrics.py`

- [ ] **Step 1: Write parse_layout_metrics.py**

Create `benchmarks/scripts/parse_layout_metrics.py`:

```python
#!/usr/bin/env python3
"""Parse ALIGN output LEF and GDS for layout quality metrics."""

import re, sys, json, pathlib, struct

def parse_lef_area(lef_path):
    """Extract MACRO SIZE from top-level LEF. Returns (width, height, area) in µm²."""
    text = pathlib.Path(lef_path).read_text()
    m = re.search(r'SIZE\s+([\d.]+)\s+BY\s+([\d.]+)', text)
    if not m:
        return None, None, None
    w, h = float(m.group(1)), float(m.group(2))
    return w, h, round(w * h, 4)

def parse_gds_metrics(gds_path, via_layers):
    """
    Parse binary GDS II file for total wirelength and via count.
    via_layers: set of GDS layer numbers that represent vias (e.g. {12, 14, 16, 17, 22})
    wire_layers: set of GDS layer numbers for routing metals
    Returns dict with wirelength_um and via_count.
    """
    wire_layers = {13, 15, 19, 21, 23}  # M1-M5
    via_layers = {12, 14, 16, 17, 22}   # V0-V4

    total_wire_length = 0.0  # in database units, converted later
    via_count = 0
    db_unit = 1e-9  # default, overridden by UNITS record

    with open(gds_path, 'rb') as f:
        data = f.read()

    i = 0
    current_layer = None
    in_path = False
    in_sref = False

    while i < len(data) - 4:
        length = struct.unpack_from('>H', data, i)[0]
        if length < 4:
            i += 4
            continue
        rtype = struct.unpack_from('>H', data, i + 2)[0]
        payload = data[i + 4: i + length]

        record_type = rtype >> 8

        # UNITS record (0x03): bytes 0-7 = user units, bytes 8-15 = meters/db-unit
        if record_type == 0x03 and len(payload) >= 16:
            # db_unit in meters (IEEE 754 double, big-endian)
            db_unit = struct.unpack_from('>d', payload, 8)[0]

        # LAYER record (0x0D)
        elif record_type == 0x0D and len(payload) >= 2:
            current_layer = struct.unpack_from('>H', payload)[0]

        # PATH record begin (0x09)
        elif record_type == 0x09:
            in_path = True

        # XY record (0x10) — coordinates of current element
        elif record_type == 0x10 and in_path and current_layer in wire_layers:
            coords = struct.unpack_from('>' + 'i' * (len(payload) // 4), payload)
            # Sum segment lengths along the path
            pts = [(coords[j], coords[j+1]) for j in range(0, len(coords)-1, 2)]
            for j in range(len(pts) - 1):
                dx = abs(pts[j+1][0] - pts[j][0])
                dy = abs(pts[j+1][1] - pts[j][1])
                total_wire_length += (dx + dy) * db_unit * 1e6  # convert to µm

        # SREF (structure reference = placed cell, used for vias as cells)
        elif record_type == 0x0A:
            in_sref = True

        # ENDEL (0x11) — end of element
        elif record_type == 0x11:
            in_path = False
            in_sref = False

        # BOX or BOUNDARY on via layer → count vias
        elif record_type in (0x08, 0x06) and current_layer in via_layers:
            via_count += 1

        i += length

    return {
        'wirelength_um': round(total_wire_length, 2),
        'via_count': via_count,
    }

def main():
    circuit = sys.argv[1]
    work_dir = pathlib.Path(sys.argv[2])
    runtime_ms = int(sys.argv[3])
    version = sys.argv[4]

    # Find LEF file
    lef_files = list(work_dir.glob(f'{circuit}.lef'))
    if not lef_files:
        lef_files = list(work_dir.rglob('*.lef'))
    if not lef_files:
        print(f'ERROR: no LEF file found in {work_dir}', file=sys.stderr)
        sys.exit(1)
    lef_path = lef_files[0]

    # Find GDS file (binary .gds preferred, fall back to largest file)
    gds_files = list(work_dir.rglob('*.gds'))
    gds_metrics = {'wirelength_um': None, 'via_count': None}
    if gds_files:
        try:
            gds_metrics = parse_gds_metrics(str(gds_files[0]), via_layers={12,14,16,17,22})
        except Exception as e:
            print(f'WARNING: GDS parse failed: {e}', file=sys.stderr)

    w, h, area = parse_lef_area(str(lef_path))

    metrics = {
        'circuit': circuit,
        'version': version,
        'area_um2': area,
        'cell_width_um': w,
        'cell_height_um': h,
        'wirelength_um': gds_metrics['wirelength_um'],
        'via_count': gds_metrics['via_count'],
        'runtime_s': round(runtime_ms / 1000, 2),
    }

    out_path = work_dir / 'layout_metrics.json'
    out_path.write_text(json.dumps(metrics, indent=2))
    print(json.dumps(metrics, indent=2))

if __name__ == '__main__':
    main()
```

- [ ] **Step 2: Write run_align.sh**

Create `benchmarks/scripts/run_align.sh`:

```bash
#!/usr/bin/env bash
# run_align.sh <circuit> <work_dir> <align_home> <version>
# Runs ALIGN, writes layout_metrics.json to work_dir
set -euo pipefail

CIRCUIT="$1"
WORK_DIR="$2"
ALIGN_HOME="$3"
VERSION="${4:-unknown}"
PDK="FinFET14nm_Mock_PDK"

mkdir -p "$WORK_DIR"
cd "$WORK_DIR"

echo "[run_align] Running ALIGN on ${CIRCUIT} ..."
START_MS=$(python3 -c "import time; print(int(time.time()*1000))")

python3 -m align \
  "${ALIGN_HOME}/examples/${CIRCUIT}" \
  -f "${ALIGN_HOME}/examples/${CIRCUIT}/${CIRCUIT}.sp" \
  -s "${CIRCUIT}" \
  -p "${ALIGN_HOME}/pdks/${PDK}" \
  2>&1

END_MS=$(python3 -c "import time; print(int(time.time()*1000))")
RUNTIME_MS=$(( END_MS - START_MS ))

echo "[run_align] Done in ${RUNTIME_MS} ms"
echo "[run_align] Output files:"
ls -lh "${WORK_DIR}"/ 2>/dev/null || true

# Extract layout metrics from LEF + GDS
python3 "${ALIGN_HOME}/benchmarks/scripts/parse_layout_metrics.py" \
  "$CIRCUIT" "$WORK_DIR" "$RUNTIME_MS" "$VERSION"
```

- [ ] **Step 3: Make scripts executable**

```bash
chmod +x benchmarks/scripts/run_align.sh
```

- [ ] **Step 4: Smoke test locally (requires ALIGN installed from source)**

```bash
mkdir -p /tmp/bench_test/buffer
bash benchmarks/scripts/run_align.sh buffer /tmp/bench_test/buffer $(pwd) v0.9.8
```

Expected output: `layout_metrics.json` in `/tmp/bench_test/buffer/` with non-null `area_um2` and `runtime_s`.

- [ ] **Step 5: Commit**

```bash
git add benchmarks/scripts/run_align.sh benchmarks/scripts/parse_layout_metrics.py
git commit -m "feat: add run_align.sh and LEF/GDS metric parser"
```

---

## Task 5: run_extraction.sh — Magic GDS → extracted SPICE

**What it does:** Takes the GDS from the ALIGN work directory, runs Magic headlessly with the stub tech file, writes `extracted.spice` to the work directory.

**Files:**
- Create: `benchmarks/scripts/run_extraction.sh`

- [ ] **Step 1: Write run_extraction.sh**

Create `benchmarks/scripts/run_extraction.sh`:

```bash
#!/usr/bin/env bash
# run_extraction.sh <circuit> <work_dir> <align_home>
# Runs Magic extraction on ALIGN GDS output → extracted.spice
set -euo pipefail

CIRCUIT="$1"
WORK_DIR="$2"
ALIGN_HOME="$3"
TECH_DIR="${ALIGN_HOME}/benchmarks/magic_tech/FinFET14nm_Mock_PDK"

# Find GDS file in work dir
GDS_FILE=$(find "$WORK_DIR" -name "*.gds" | head -1)
if [ -z "$GDS_FILE" ]; then
  echo "[run_extraction] ERROR: no .gds file found in ${WORK_DIR}" >&2
  echo "[run_extraction] Contents of work dir:" >&2
  ls -lh "$WORK_DIR" >&2
  exit 1
fi

echo "[run_extraction] Extracting from: ${GDS_FILE}"

# Run Magic headlessly in work_dir so .ext files land there
cd "$WORK_DIR"
export INPUT_GDS="$GDS_FILE"
export OUTPUT_DIR="$WORK_DIR"

magic \
  -dnull \
  -noconsole \
  -rcfile "${TECH_DIR}/FinFET14nm.magicrc" \
  < "${TECH_DIR}/ext2spice.tcl" \
  2>&1

if [ ! -f "${WORK_DIR}/extracted.spice" ]; then
  echo "[run_extraction] ERROR: extracted.spice not created" >&2
  exit 1
fi

echo "[run_extraction] Extraction complete: ${WORK_DIR}/extracted.spice"
wc -l "${WORK_DIR}/extracted.spice"
```

- [ ] **Step 2: Make executable**

```bash
chmod +x benchmarks/scripts/run_extraction.sh
```

- [ ] **Step 3: Smoke test (requires Magic installed and ALIGN run from Task 4)**

```bash
bash benchmarks/scripts/run_extraction.sh buffer /tmp/bench_test/buffer $(pwd)
```

Expected: `/tmp/bench_test/buffer/extracted.spice` exists and has `R` and `C` elements.

```bash
grep -c "^R" /tmp/bench_test/buffer/extracted.spice
grep -c "^C" /tmp/bench_test/buffer/extracted.spice
```

- [ ] **Step 4: Commit**

```bash
git add benchmarks/scripts/run_extraction.sh
git commit -m "feat: add Magic extraction script"
```

---

## Task 6: run_simulation.sh — ngspice → metrics JSON

**What it does:** Copies the testbench into the work directory (so relative `.include ../../extracted.spice` resolves), runs ngspice in batch mode, parses `.measure` outputs, merges with layout metrics into final `metrics.json`.

**Files:**
- Create: `benchmarks/scripts/run_simulation.sh`
- Create: `benchmarks/scripts/parse_sim_metrics.py`

- [ ] **Step 1: Write parse_sim_metrics.py**

ngspice batch mode prints measurements like:
```
gain_db              =  2.345678e+01 at= ...
ugbw_mhz             =  1.234567e+02 ...
```

Create `benchmarks/scripts/parse_sim_metrics.py`:

```python
#!/usr/bin/env python3
"""Parse ngspice batch output for .measure results, merge with layout metrics."""

import re, sys, json, pathlib

def parse_ngspice_output(ngspice_stdout):
    """Extract .measure results from ngspice stdout. Returns dict of name→value."""
    results = {}
    # ngspice prints: "measure_name  =  value  ..."
    for line in ngspice_stdout.splitlines():
        m = re.match(r'^\s*([\w_]+)\s*=\s*([-+]?[\d.]+(?:[eE][-+]?\d+)?)', line)
        if m:
            name = m.group(1).lower().strip()
            try:
                results[name] = float(m.group(2))
            except ValueError:
                pass
    return results

def scale_sim_metrics(raw, circuit):
    """Convert raw ngspice values to display units (ns, MHz, dB, µW)."""
    scaled = {}
    unit_map = {
        # buffer
        'tphl_ns': ('tphl_ns', 1e9),    # s → ns
        'tplh_ns': ('tplh_ns', 1e9),
        # ota / amplifiers
        'gain_db':        ('gain_db',        1.0),
        'ugbw_mhz':       ('ugbw_mhz',       1e-6),  # Hz → MHz
        'phase_at_ugbw':  ('phase_margin_deg', lambda v: 180.0 + v),
        'bandwidth_mhz':  ('bandwidth_mhz',  1e-6),
        'cmrr_db':        ('cmrr_db',        1.0),
        # comparator
        'regen_time_ns':  ('regen_time_ns',  1e9),
        'static_power_uw':('static_power_uw', 1.0),  # already µW from param
        # VGA
        'gain_range_db':  ('gain_range_db',  1.0),
        # SCF
        'f3db_mhz':       ('f3db_mhz',       1e-6),
        'passband_ripple_db': ('passband_ripple_db', 1.0),
    }
    for raw_name, (out_name, scale) in unit_map.items():
        if raw_name in raw:
            val = raw[raw_name]
            if callable(scale):
                scaled[out_name] = round(scale(val), 4)
            else:
                scaled[out_name] = round(val * scale, 4)
    return scaled

def main():
    circuit = sys.argv[1]
    work_dir = pathlib.Path(sys.argv[2])
    ngspice_output_file = sys.argv[3]  # path to captured ngspice stdout

    # Load ngspice output
    ngspice_out = pathlib.Path(ngspice_output_file).read_text()
    raw = parse_ngspice_output(ngspice_out)
    sim_metrics = scale_sim_metrics(raw, circuit)

    # Load existing layout metrics
    layout_file = work_dir / 'layout_metrics.json'
    if layout_file.exists():
        combined = json.loads(layout_file.read_text())
    else:
        combined = {'circuit': circuit}

    combined.update(sim_metrics)

    out_path = work_dir / 'metrics.json'
    out_path.write_text(json.dumps(combined, indent=2))
    print(json.dumps(combined, indent=2))

if __name__ == '__main__':
    main()
```

- [ ] **Step 2: Write run_simulation.sh**

Create `benchmarks/scripts/run_simulation.sh`:

```bash
#!/usr/bin/env bash
# run_simulation.sh <circuit> <work_dir> <align_home> <version>
# Runs ngspice on testbench → metrics.json
set -euo pipefail

CIRCUIT="$1"
WORK_DIR="$2"
ALIGN_HOME="$3"
VERSION="${4:-unknown}"
TB_SRC="${ALIGN_HOME}/benchmarks/testbenches/${CIRCUIT}/tb.sp"

if [ ! -f "$TB_SRC" ]; then
  echo "[run_simulation] ERROR: testbench not found: ${TB_SRC}" >&2
  exit 1
fi

if [ ! -f "${WORK_DIR}/extracted.spice" ]; then
  echo "[run_simulation] ERROR: extracted.spice not found — run extraction first" >&2
  exit 1
fi

echo "[run_simulation] Running ngspice for ${CIRCUIT} ..."

# Copy testbench so relative .include paths resolve from work_dir
cp "$TB_SRC" "${WORK_DIR}/tb.sp"

NGSPICE_OUT="${WORK_DIR}/ngspice_out.txt"

ngspice -b "${WORK_DIR}/tb.sp" \
  2>&1 | tee "$NGSPICE_OUT" || true
# 'true' prevents exit on ngspice non-zero exit (measure failures are non-fatal)

echo "[run_simulation] ngspice done."

python3 "${ALIGN_HOME}/benchmarks/scripts/parse_sim_metrics.py" \
  "$CIRCUIT" "$WORK_DIR" "$NGSPICE_OUT"
```

- [ ] **Step 3: Make executable**

```bash
chmod +x benchmarks/scripts/run_simulation.sh
```

- [ ] **Step 4: Smoke test (requires extraction from Task 5)**

```bash
bash benchmarks/scripts/run_simulation.sh buffer /tmp/bench_test/buffer $(pwd) v0.9.8
cat /tmp/bench_test/buffer/metrics.json
```

Expected: `metrics.json` with both layout fields (`area_um2`, `runtime_s`) and simulation fields (`tphl_ns`, `tplh_ns`).

If simulation measurements show `failed` in ngspice output, check `/tmp/bench_test/buffer/ngspice_out.txt` for convergence errors. Common fixes:
- Reduce `.ac` frequency range upper bound to `1g` instead of `10g`
- Add `.ic` statement to set initial conditions
- Increase `GMIN` to `1e-10`

- [ ] **Step 5: Commit**

```bash
git add benchmarks/scripts/run_simulation.sh benchmarks/scripts/parse_sim_metrics.py
git commit -m "feat: add ngspice simulation runner and metric parser"
```

---

## Task 7: aggregate.py — merge artifacts and detect regressions

**What it does:** Reads all per-circuit `metrics.json` files from the artifacts directory, merges into one release entry, appends to `history.json`, writes per-version `results.json`, detects regressions.

**Files:**
- Create: `benchmarks/scripts/aggregate.py`

- [ ] **Step 1: Write aggregate.py**

Create `benchmarks/scripts/aggregate.py`:

```python
#!/usr/bin/env python3
"""
aggregate.py <artifacts_dir> <history_json> <version> <config_json>

artifacts_dir: directory containing metrics-<circuit>/metrics.json files
history_json:  path to history.json on gh-pages branch (created if absent)
version:       release tag string, e.g. "v0.9.8"
config_json:   path to benchmarks/config.json
"""
import json, os, sys, glob, pathlib

def load_artifacts(artifacts_dir):
    results = {}
    for f in glob.glob(f"{artifacts_dir}/**/metrics.json", recursive=True):
        with open(f) as fp:
            data = json.load(fp)
        circuit = data.get('circuit')
        if circuit:
            results[circuit] = data
    return results

def check_regressions(current, previous, thresholds):
    """Compare current vs previous release. Higher = worse for all metrics."""
    warn_pct = thresholds['warning_pct']
    fail_pct = thresholds['failure_pct']
    warnings, failures = [], []

    for circuit, metrics in current.items():
        if circuit not in previous:
            continue
        prev = previous[circuit]
        for key, val in metrics.items():
            if key in ('circuit', 'version', 'timestamp'):
                continue
            if not isinstance(val, (int, float)) or val is None:
                continue
            prev_val = prev.get(key)
            if not isinstance(prev_val, (int, float)) or prev_val is None or prev_val <= 0:
                continue
            pct = (val - prev_val) / prev_val * 100
            entry = {'circuit': circuit, 'metric': key,
                     'current': val, 'previous': prev_val,
                     'pct_change': round(pct, 2)}
            if pct > fail_pct:
                failures.append(entry)
            elif pct > warn_pct:
                warnings.append(entry)

    return warnings, failures

def main():
    if len(sys.argv) != 5:
        print("Usage: aggregate.py <artifacts_dir> <history_json> <version> <config_json>")
        sys.exit(1)

    artifacts_dir, history_file, version, config_file = sys.argv[1:]

    with open(config_file) as f:
        config = json.load(f)

    current = load_artifacts(artifacts_dir)
    if not current:
        print(f"ERROR: no metrics.json files found in {artifacts_dir}", file=sys.stderr)
        sys.exit(1)

    history = []
    history_path = pathlib.Path(history_file)
    history_path.parent.mkdir(parents=True, exist_ok=True)
    if history_path.exists():
        with open(history_path) as f:
            history = json.load(f)

    previous = {}
    if history:
        for c in history[-1].get('circuits', []):
            previous[c['circuit']] = c

    warnings, failures = check_regressions(current, previous, config['regression_thresholds'])

    release = {
        'version': version,
        'circuits': list(current.values()),
        'regressions': {'warnings': warnings, 'failures': failures}
    }
    history.append(release)

    with open(history_path, 'w') as f:
        json.dump(history, f, indent=2)

    # Write per-version results
    version_dir = history_path.parent / version
    version_dir.mkdir(parents=True, exist_ok=True)
    with open(version_dir / 'results.json', 'w') as f:
        json.dump(release, f, indent=2)

    print(f"Aggregated {len(current)} circuits for {version}")
    if warnings:
        print(f"WARNINGS ({len(warnings)}): {json.dumps(warnings)}")
    if failures:
        print(f"FAILURES ({len(failures)}): {json.dumps(failures)}", file=sys.stderr)
        sys.exit(1)

if __name__ == '__main__':
    main()
```

- [ ] **Step 2: Test aggregate.py locally**

```bash
# Create mock artifact structure
mkdir -p /tmp/agg_test/metrics-buffer
cat > /tmp/agg_test/metrics-buffer/metrics.json <<'EOF'
{"circuit": "buffer", "version": "v0.9.8", "area_um2": 12.5, "wirelength_um": 45.3,
 "via_count": 18, "runtime_s": 4.2, "tphl_ns": 0.12, "tplh_ns": 0.11}
EOF

mkdir -p /tmp/agg_test/gh-pages/benchmarks
echo '[]' > /tmp/agg_test/gh-pages/benchmarks/history.json

python3 benchmarks/scripts/aggregate.py \
  /tmp/agg_test/metrics-buffer \
  /tmp/agg_test/gh-pages/benchmarks/history.json \
  v0.9.8 \
  benchmarks/config.json

cat /tmp/agg_test/gh-pages/benchmarks/history.json
```

Expected: history.json contains one entry for v0.9.8 with buffer circuit data.

- [ ] **Step 3: Commit**

```bash
git add benchmarks/scripts/aggregate.py
git commit -m "feat: add benchmark aggregation and regression detection script"
```

---

## Task 8: render_dashboard.py — static HTML dashboard

**What it does:** Reads `history.json`, generates a self-contained `index.html` with Chart.js trend lines for all circuits and metrics.

**Files:**
- Create: `benchmarks/scripts/render_dashboard.py`

- [ ] **Step 1: Write render_dashboard.py**

Create `benchmarks/scripts/render_dashboard.py`:

```python
#!/usr/bin/env python3
"""
render_dashboard.py <history_json> <output_html>
Generates static Chart.js dashboard from benchmark history.
"""
import json, sys, pathlib

LAYOUT_METRICS = ['area_um2', 'wirelength_um', 'via_count', 'runtime_s']
SIM_METRICS = {
    'buffer':                   ['tphl_ns', 'tplh_ns'],
    'five_transistor_ota':      ['gain_db', 'ugbw_mhz', 'phase_margin_deg'],
    'current_mirror_ota':       ['gain_db', 'bandwidth_mhz'],
    'high_speed_comparator':    ['regen_time_ns', 'static_power_uw'],
    'variable_gain_amplifier':  ['gain_db', 'bandwidth_mhz'],
    'switched_capacitor_filter':['f3db_mhz', 'passband_ripple_db'],
}

HTML_TEMPLATE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<title>ALIGN Release Benchmarks</title>
<script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.0/dist/chart.umd.min.js"></script>
<style>
  * { box-sizing: border-box; }
  body { font-family: -apple-system, sans-serif; max-width: 1100px; margin: 0 auto; padding: 20px; color: #333; }
  h1 { border-bottom: 2px solid #007bff; padding-bottom: 8px; }
  .tabs { display: flex; gap: 8px; margin: 16px 0; }
  .tab-btn { padding: 8px 20px; border: 1px solid #007bff; border-radius: 4px;
             background: white; color: #007bff; cursor: pointer; font-size: 14px; }
  .tab-btn.active { background: #007bff; color: white; }
  .tab { display: none; }
  .tab.active { display: block; }
  .circuit-card { border: 1px solid #ddd; border-radius: 6px; padding: 16px; margin: 12px 0; }
  .circuit-card h3 { margin-top: 0; color: #007bff; font-size: 16px; }
  .charts-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(280px, 1fr)); gap: 12px; }
  .chart-wrap { position: relative; height: 140px; }
  .chart-label { font-size: 11px; color: #666; margin-bottom: 2px; }
  .regression-table { width: 100%; border-collapse: collapse; margin-top: 12px; font-size: 13px; }
  .regression-table th { background: #f5f5f5; padding: 6px 10px; text-align: left; border: 1px solid #ddd; }
  .regression-table td { padding: 6px 10px; border: 1px solid #ddd; }
  .warn { background: #fff3cd; }
  .fail { background: #f8d7da; }
  .ok   { background: #d4edda; }
</style>
</head>
<body>
<h1>ALIGN Release Benchmarks</h1>
<p>Post-layout metrics tracked across PyPI releases. PDK: FinFET14nm_Mock_PDK.</p>

<div class="tabs">
  <button class="tab-btn active" onclick="showTab('layout', this)">Layout Quality</button>
  <button class="tab-btn"        onclick="showTab('simulation', this)">Simulation</button>
  <button class="tab-btn"        onclick="showTab('regressions', this)">Regressions</button>
</div>

<div id="layout" class="tab active">
  <h2>Layout Quality</h2>
  <div id="layout-content"></div>
</div>

<div id="simulation" class="tab">
  <h2>Post-Layout Simulation</h2>
  <div id="sim-content"></div>
</div>

<div id="regressions" class="tab">
  <h2>Regression Summary</h2>
  <div id="reg-content"></div>
</div>

<script>
const history = __HISTORY__;
const LAYOUT_METRICS = __LAYOUT_METRICS__;
const SIM_METRICS = __SIM_METRICS__;

function showTab(name, btn) {
  document.querySelectorAll('.tab').forEach(t => t.classList.remove('active'));
  document.querySelectorAll('.tab-btn').forEach(b => b.classList.remove('active'));
  document.getElementById(name).classList.add('active');
  btn.classList.add('active');
}

const versions = history.map(r => r.version);
const COLORS = ['#007bff','#28a745','#dc3545','#fd7e14','#6f42c1','#17a2b8'];

function miniChart(canvasId, label, versions, data) {
  const ctx = document.getElementById(canvasId);
  if (!ctx) return;
  new Chart(ctx, {
    type: 'line',
    data: {
      labels: versions,
      datasets: [{ label, data,
        borderColor: '#007bff', backgroundColor: 'rgba(0,123,255,0.08)',
        tension: 0.2, pointRadius: 3, fill: true }]
    },
    options: {
      responsive: true, maintainAspectRatio: false,
      plugins: { legend: { display: false } },
      scales: {
        x: { ticks: { font: { size: 10 } } },
        y: { ticks: { font: { size: 10 } } }
      }
    }
  });
}

function getVals(circuit, metric) {
  return history.map(r => {
    const c = (r.circuits || []).find(x => x.circuit === circuit);
    return (c && c[metric] != null) ? c[metric] : null;
  });
}

function buildSection(containerId, circuits, metricsMap) {
  const container = document.getElementById(containerId);
  circuits.forEach((circuit, ci) => {
    const metrics = Array.isArray(metricsMap) ? metricsMap : (metricsMap[circuit] || []);
    const card = document.createElement('div');
    card.className = 'circuit-card';
    card.innerHTML = '<h3>' + circuit.replace(/_/g,' ') + '</h3><div class="charts-grid"></div>';
    const grid = card.querySelector('.charts-grid');
    metrics.forEach(metric => {
      const id = 'ch_' + circuit + '_' + metric;
      const wrap = document.createElement('div');
      wrap.innerHTML = '<div class="chart-label">' + metric + '</div><div class="chart-wrap"><canvas id="' + id + '"></canvas></div>';
      grid.appendChild(wrap);
      const vals = getVals(circuit, metric);
      setTimeout(() => miniChart(id, metric, versions, vals), 0);
    });
    container.appendChild(card);
  });
}

// Get unique circuits from history
const circuits = history.length > 0
  ? [...new Set(history.flatMap(r => (r.circuits||[]).map(c => c.circuit)))]
  : [];

buildSection('layout-content', circuits, LAYOUT_METRICS);
buildSection('sim-content', circuits, SIM_METRICS);

// Regression table
const regContainer = document.getElementById('reg-content');
history.slice().reverse().forEach(release => {
  const regs = release.regressions || {};
  const all = [...(regs.failures||[]).map(r=>({...r,level:'fail'})),
               ...(regs.warnings||[]).map(r=>({...r,level:'warn'}))];
  const section = document.createElement('div');
  section.innerHTML = '<h3>' + release.version + '</h3>';
  if (!all.length) {
    section.innerHTML += '<p style="color:#28a745">&#10003; No regressions detected.</p>';
  } else {
    let html = '<table class="regression-table"><tr><th>Circuit</th><th>Metric</th><th>Previous</th><th>Current</th><th>Change %</th></tr>';
    all.forEach(r => {
      html += '<tr class="' + r.level + '"><td>' + r.circuit + '</td><td>' + r.metric +
              '</td><td>' + r.previous + '</td><td>' + r.current +
              '</td><td>' + (r.pct_change > 0 ? '+' : '') + r.pct_change + '%</td></tr>';
    });
    html += '</table>';
    section.innerHTML += html;
  }
  regContainer.appendChild(section);
});
</script>
</body>
</html>
"""

def main():
    if len(sys.argv) != 3:
        print("Usage: render_dashboard.py <history_json> <output_html>")
        sys.exit(1)

    history_file, output_file = sys.argv[1], sys.argv[2]

    with open(history_file) as f:
        history = json.load(f)

    html = HTML_TEMPLATE \
        .replace('__HISTORY__', json.dumps(history)) \
        .replace('__LAYOUT_METRICS__', json.dumps(LAYOUT_METRICS)) \
        .replace('__SIM_METRICS__', json.dumps(SIM_METRICS))

    out = pathlib.Path(output_file)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(html)
    print(f"Dashboard written to {output_file} ({out.stat().st_size} bytes)")

if __name__ == '__main__':
    main()
```

- [ ] **Step 2: Test render locally**

```bash
python3 benchmarks/scripts/render_dashboard.py \
  /tmp/agg_test/gh-pages/benchmarks/history.json \
  /tmp/bench_dashboard/index.html

# Open in browser to visually verify
open /tmp/bench_dashboard/index.html   # macOS
# xdg-open /tmp/bench_dashboard/index.html  # Linux
```

Expected: browser shows ALIGN Benchmark Dashboard with Layout Quality tab displaying a chart for buffer.

- [ ] **Step 3: Commit**

```bash
git add benchmarks/scripts/render_dashboard.py
git commit -m "feat: add Chart.js benchmark dashboard renderer"
```

---

## Task 9: benchmark.yml — GitHub Actions workflow

**Files:**
- Create: `.github/workflows/benchmark.yml`

- [ ] **Step 1: Initialize gh-pages branch (one-time setup)**

Run this once from the repo root to create the gh-pages branch:

```bash
git checkout --orphan gh-pages-init
git rm -rf .
mkdir -p benchmarks
echo '[]' > benchmarks/history.json
git add benchmarks/history.json
git commit -m "chore: initialize gh-pages for benchmark dashboard"
git push origin HEAD:gh-pages
git checkout feat/release-benchmarks
```

Then in the GitHub repo settings → Pages, set source to `gh-pages` branch, `/ (root)` folder.

- [ ] **Step 2: Write benchmark.yml**

Create `.github/workflows/benchmark.yml`:

```yaml
name: Release Benchmarks

on:
  workflow_run:
    workflows: ["Build and Publish Wheels"]
    types: [completed]
    branches: [master]

jobs:
  benchmark:
    if: ${{ github.event.workflow_run.conclusion == 'success' }}
    runs-on: ubuntu-latest
    strategy:
      fail-fast: false
      matrix:
        circuit:
          - buffer
          - five_transistor_ota
          - current_mirror_ota
          - high_speed_comparator
          - variable_gain_amplifier
          - switched_capacitor_filter

    steps:
      - uses: actions/checkout@v4
        with:
          submodules: recursive

      - name: Resolve released version tag
        id: version
        run: |
          git fetch --tags --quiet
          SHA="${{ github.event.workflow_run.head_sha }}"
          VERSION=$(git tag --points-at "$SHA" | grep '^v' | head -1)
          if [ -z "$VERSION" ]; then
            echo "ERROR: no v* tag found for SHA $SHA" >&2
            exit 1
          fi
          echo "version=${VERSION}" >> "$GITHUB_OUTPUT"

      - name: Cache Magic build
        id: cache-magic
        uses: actions/cache@v4
        with:
          path: ~/.local/magic
          key: magic-7.3.456-ubuntu-22.04-v1

      - name: Install Magic build dependencies
        if: steps.cache-magic.outputs.cache-hit != 'true'
        run: |
          sudo apt-get update -qq
          sudo apt-get install -y --no-install-recommends \
            tcl-dev tk-dev m4 csh libglu1-mesa-dev freeglut3-dev \
            libcairo2-dev libncurses-dev

      - name: Build Magic from source
        if: steps.cache-magic.outputs.cache-hit != 'true'
        run: |
          git clone --depth 1 --branch 7.3.456 \
            https://github.com/RTimothyEdwards/magic.git magic-src
          cd magic-src
          ./configure --prefix="$HOME/.local" --without-x
          make -j$(nproc)
          make install

      - name: Install ngspice and Python deps
        run: |
          sudo apt-get install -y --no-install-recommends ngspice
          pip install --quiet align-analoglayout==${{ steps.version.outputs.version }}

      - name: Run ALIGN layout
        run: |
          export PATH="$HOME/.local/bin:$PATH"
          mkdir -p work/${{ matrix.circuit }}
          bash benchmarks/scripts/run_align.sh \
            ${{ matrix.circuit }} \
            $(pwd)/work/${{ matrix.circuit }} \
            $(pwd) \
            ${{ steps.version.outputs.version }}

      - name: Run Magic extraction
        run: |
          export PATH="$HOME/.local/bin:$PATH"
          bash benchmarks/scripts/run_extraction.sh \
            ${{ matrix.circuit }} \
            $(pwd)/work/${{ matrix.circuit }} \
            $(pwd)

      - name: Run ngspice simulation
        run: |
          bash benchmarks/scripts/run_simulation.sh \
            ${{ matrix.circuit }} \
            $(pwd)/work/${{ matrix.circuit }} \
            $(pwd) \
            ${{ steps.version.outputs.version }}

      - name: Upload metrics artifact
        uses: actions/upload-artifact@v4
        with:
          name: metrics-${{ matrix.circuit }}
          path: work/${{ matrix.circuit }}/metrics.json

  aggregate-and-publish:
    needs: benchmark
    runs-on: ubuntu-latest
    permissions:
      contents: write

    steps:
      - name: Checkout source (for scripts + config)
        uses: actions/checkout@v4
        with:
          path: source

      - name: Checkout gh-pages branch
        uses: actions/checkout@v4
        with:
          ref: gh-pages
          path: gh-pages

      - name: Download all metrics artifacts
        uses: actions/download-artifact@v4
        with:
          pattern: metrics-*
          path: artifacts/
          merge-multiple: true

      - name: Resolve released version
        id: version
        run: |
          cd source
          git fetch --tags --quiet
          SHA="${{ github.event.workflow_run.head_sha }}"
          VERSION=$(git tag --points-at "$SHA" | grep '^v' | head -1)
          echo "version=${VERSION}" >> "$GITHUB_OUTPUT"

      - name: Aggregate results
        run: |
          python3 source/benchmarks/scripts/aggregate.py \
            artifacts/ \
            gh-pages/benchmarks/history.json \
            ${{ steps.version.outputs.version }} \
            source/benchmarks/config.json

      - name: Render dashboard
        run: |
          python3 source/benchmarks/scripts/render_dashboard.py \
            gh-pages/benchmarks/history.json \
            gh-pages/benchmarks/index.html

      - name: Commit and push to gh-pages
        run: |
          cd gh-pages
          git config user.name  "github-actions[bot]"
          git config user.email "github-actions[bot]@users.noreply.github.com"
          git add benchmarks/
          git diff --cached --quiet && echo "No changes to commit" && exit 0
          git commit -m "benchmarks: add metrics for ${{ steps.version.outputs.version }}"
          git push
```

- [ ] **Step 3: Commit workflow**

```bash
git add .github/workflows/benchmark.yml
git commit -m "feat: add release benchmark GitHub Actions workflow"
```

---

## Task 10: End-to-end dry run and PR

- [ ] **Step 1: Verify all scripts are executable**

```bash
ls -la benchmarks/scripts/
# All .sh files should show -rwxr-xr-x
```

- [ ] **Step 2: Check all files exist**

```bash
find benchmarks/ -type f | sort
```

Expected output should include all 16 files from the file map at the top of this plan.

- [ ] **Step 3: Dry run benchmark.yml with workflow_dispatch (optional)**

Add `workflow_dispatch:` to `benchmark.yml` triggers temporarily:

```yaml
on:
  workflow_dispatch:
    inputs:
      version:
        description: 'Version tag to benchmark'
        default: 'v0.9.8'
  workflow_run:
    ...
```

Then trigger manually from GitHub Actions UI with version=v0.9.8. Remove the `workflow_dispatch` input after confirming the end-to-end flow works.

- [ ] **Step 4: Push branch and open PR**

```bash
git push origin feat/release-benchmarks
gh pr create \
  --title "feat: add post-layout benchmark metrics system for PyPI releases" \
  --body "Implements the benchmark pipeline described in docs/superpowers/specs/2026-06-17-release-benchmarks-design.md.

## What this adds
- Magic tech files for FinFET14nm_Mock_PDK (GDS layer mapping + stub RC values)
- ngspice testbenches for 6 representative circuits
- Scripts: run_align.sh, run_extraction.sh, run_simulation.sh, aggregate.py, render_dashboard.py
- benchmark.yml: parallel matrix workflow triggered after PyPI publish
- Dashboard published to GitHub Pages after every release

## Dashboard URL (after first run)
https://align-analoglayout.github.io/ALIGN-public/benchmarks/
" \
  --base master
```

---

## Self-Review Notes

- **GDS parse in parse_layout_metrics.py**: The binary GDS parser is minimal. If ALIGN outputs GDS in JSON format (`.gds.json`) instead of binary, `run_align.sh` will find no `.gds` file and `wirelength_um`/`via_count` will be `null`. In that case, add a conversion step using `gdspy` (`pip install gdspy`) to convert from ALIGN's JSON GDS format to binary before calling run_extraction.sh.
- **Magic cifinput syntax**: If Magic fails to read the GDS layers, check that `FinFET14nm.tech` cifinput section uses the correct syntax for the installed Magic version. Magic 7.3.x uses `layer <type> <stream_layer> <stream_datatype>` (space-separated, not `/`-separated). Adjust if needed.
- **ngspice .measure units**: The `tphl_ns` and `tplh_ns` measures in the buffer testbench are in seconds in the ngspice output; `parse_sim_metrics.py` scales them by `1e9`. Verify by checking the raw `ngspice_out.txt`.
- **phase_margin_deg**: Computed as `180 + phase_at_ugbw` from the ngspice `vp()` measurement. ngspice returns phase in degrees. If the phase margin comes out negative, the circuit is unstable in simulation (expected for some level-1 model operating points).

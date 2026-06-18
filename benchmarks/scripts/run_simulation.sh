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

cp "$TB_SRC" "${WORK_DIR}/tb.sp"

NGSPICE_OUT="${WORK_DIR}/ngspice_out.txt"

ngspice -b "${WORK_DIR}/tb.sp" \
  2>&1 | tee "$NGSPICE_OUT" || true

echo "[run_simulation] ngspice done."

python3 "${ALIGN_HOME}/benchmarks/scripts/parse_sim_metrics.py" \
  "$CIRCUIT" "$WORK_DIR" "$NGSPICE_OUT"

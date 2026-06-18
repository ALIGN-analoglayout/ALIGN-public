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

python3 "${ALIGN_HOME}/benchmarks/scripts/parse_layout_metrics.py" \
  "$CIRCUIT" "$WORK_DIR" "$RUNTIME_MS" "$VERSION"

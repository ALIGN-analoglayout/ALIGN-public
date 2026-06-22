#!/usr/bin/env bash
# run_align.sh <circuit> <work_dir> <align_home> <version> [<pdk_path> [<design_dir>]]
# Runs ALIGN, writes layout_metrics.json to work_dir
#
# Args:
#   1: circuit      - circuit name (also used as subckt)
#   2: work_dir     - output working directory
#   3: align_home   - path to ALIGN repo root
#   4: version      - version string (default: unknown)
#   5: pdk_path     - (optional) path to PDK directory
#                     default: $ALIGN_HOME/pdks/FinFET14nm_Mock_PDK
#   6: design_dir   - (optional) path to circuit design directory
#                     default: $ALIGN_HOME/examples/<circuit>
set -euo pipefail

CIRCUIT="$1"
WORK_DIR="$2"
ALIGN_HOME="$3"
VERSION="${4:-unknown}"
PDK_PATH="${5:-${ALIGN_HOME}/pdks/FinFET14nm_Mock_PDK}"
DESIGN_DIR="${6:-${ALIGN_HOME}/examples/${CIRCUIT}}"

# Derive PDK name from path for metrics parsing
PDK_NAME="$(basename "${PDK_PATH}")"

mkdir -p "$WORK_DIR"
WORK_DIR="$(realpath "$WORK_DIR")"
cd "$WORK_DIR"

echo "[run_align] Running ALIGN on ${CIRCUIT} ..."
echo "[run_align] PDK:        ${PDK_PATH}"
echo "[run_align] Design dir: ${DESIGN_DIR}"
START_MS=$(python3 -c "import time; print(int(time.time()*1000))")

[[ -d "$DESIGN_DIR" ]] || { echo "ERROR: design directory not found: $DESIGN_DIR"; exit 1; }

python3 "${ALIGN_HOME}/bin/schematic2layout.py" \
  "${DESIGN_DIR}" \
  -f "${DESIGN_DIR}/${CIRCUIT}.sp" \
  -s "${CIRCUIT}" \
  -p "${PDK_PATH}" \
  2>&1

END_MS=$(python3 -c "import time; print(int(time.time()*1000))")
RUNTIME_MS=$(( END_MS - START_MS ))

echo "[run_align] Done in ${RUNTIME_MS} ms"
echo "[run_align] Output files:"
ls -lh "${WORK_DIR}"/ 2>/dev/null || true

python3 "${ALIGN_HOME}/benchmarks/scripts/parse_layout_metrics.py" \
  "$CIRCUIT" "$WORK_DIR" "$RUNTIME_MS" "$VERSION" --pdk "${PDK_NAME}"

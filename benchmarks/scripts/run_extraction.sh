#!/usr/bin/env bash
# run_extraction.sh <circuit> <work_dir> <tech_dir>
# Runs Magic extraction on ALIGN GDS output → extracted.spice
set -euo pipefail

CIRCUIT="$1"
WORK_DIR="$(realpath "$2")"
TECH_DIR="$(realpath "$3")"

# Prefer the plain .gds over .python.gds
GDS_FILE=$(find "$WORK_DIR" -name "*.gds" ! -name "*.python.gds" | head -1)
if [ -z "$GDS_FILE" ]; then
  GDS_FILE=$(find "$WORK_DIR" -name "*.gds" | head -1)
fi
if [ -z "$GDS_FILE" ]; then
  echo "[run_extraction] ERROR: no .gds file found in ${WORK_DIR}" >&2
  ls -lh "$WORK_DIR" >&2
  exit 1
fi

echo "[run_extraction] Extracting from: ${GDS_FILE}"

TECH_FILE=$(find "${TECH_DIR}" -name "*.tech" | head -1)
[[ -n "$TECH_FILE" ]] || { echo "ERROR: no .tech file found in ${TECH_DIR}"; exit 1; }

export INPUT_GDS="$GDS_FILE"
export OUTPUT_DIR="$WORK_DIR"

magic \
  -dnull \
  -noconsole \
  -T "${TECH_FILE}" \
  < "${TECH_DIR}/ext2spice.tcl" \
  2>&1

if [ ! -f "${WORK_DIR}/extracted.spice" ]; then
  echo "[run_extraction] ERROR: extracted.spice not created" >&2
  exit 1
fi

echo "[run_extraction] Extraction complete: ${WORK_DIR}/extracted.spice"
wc -l "${WORK_DIR}/extracted.spice"

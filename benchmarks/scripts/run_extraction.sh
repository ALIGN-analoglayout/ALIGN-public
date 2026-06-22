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

MAGICRC=$(find "${TECH_DIR}" -name "*.magicrc" | head -1)
[[ -n "$MAGICRC" ]] || { echo "ERROR: no .magicrc found in ${TECH_DIR}"; exit 1; }

export INPUT_GDS="$GDS_FILE"
export OUTPUT_DIR="$WORK_DIR"
# MAGICPATH tells Magic where to find the .tech file referenced in magicrc
export MAGICPATH="$TECH_DIR"

magic \
  -dnull \
  -noconsole \
  -rcfile "${MAGICRC}" \
  < "${TECH_DIR}/ext2spice.tcl" \
  2>&1

if [ ! -f "${WORK_DIR}/extracted.spice" ]; then
  echo "[run_extraction] ERROR: extracted.spice not created" >&2
  exit 1
fi

echo "[run_extraction] Extraction complete: ${WORK_DIR}/extracted.spice"
wc -l "${WORK_DIR}/extracted.spice"

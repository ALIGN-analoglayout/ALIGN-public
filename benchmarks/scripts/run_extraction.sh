#!/usr/bin/env bash
# run_extraction.sh <circuit> <work_dir> <align_home>
# Runs Magic extraction on ALIGN GDS output → extracted.spice
set -euo pipefail

CIRCUIT="$1"
WORK_DIR="$2"
ALIGN_HOME="$3"
TECH_DIR="${ALIGN_HOME}/benchmarks/magic_tech/FinFET14nm_Mock_PDK"

GDS_FILE=$(find "$WORK_DIR" -name "*.gds" | head -1)
if [ -z "$GDS_FILE" ]; then
  echo "[run_extraction] ERROR: no .gds file found in ${WORK_DIR}" >&2
  echo "[run_extraction] Contents of work dir:" >&2
  ls -lh "$WORK_DIR" >&2
  exit 1
fi

echo "[run_extraction] Extracting from: ${GDS_FILE}"

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

#!/usr/bin/env bash
#
# Consumer side of ALIGN's C++ dependency binary cache.
#
# Downloads the prebuilt COIN-OR/Cbc + SuperLU bundle that matches this
# checkout's dependency signature and current platform, extracts it, and prints
# the environment variables CMake needs to consume it:
#
#   ALIGN_ILP_PATH      -> picked up by ilpif.cmake   (prebuilt solver libs)
#   ALIGN_SUPERLU_PATH  -> picked up by superlu.cmake (prebuilt SuperLU)
#
# Designed to be safe in CI: if the matching asset is missing (e.g. a freshly
# bumped dependency that hasn't been published yet) or the download fails, this
# script exits 0 without exporting anything, so the CMake build transparently
# falls back to compiling the dependency from source.
#
# Usage:
#   # Extract into $1 (default /tmp/align-cpp-deps) and echo export lines:
#   eval "$(ci/fetch_cpp_deps.sh [DEST_DIR])"
#
# The export lines are written to stdout; all logging goes to stderr so the
# `eval` above only ever consumes export statements.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=ci/cpp_deps_common.sh
source "${SCRIPT_DIR}/cpp_deps_common.sh"

DEST_DIR="${1:-/tmp/align-cpp-deps}"

log() { echo "[fetch_cpp_deps] $*" >&2; }

asset="$(cpp_deps_asset_name)"
url="$(cpp_deps_asset_url)"
log "platform=$(cpp_deps_platform) signature=$(cpp_deps_signature)"
log "looking for ${ALIGN_CPP_DEPS_REPO}@${ALIGN_CPP_DEPS_TAG} :: ${asset}"

mkdir -p "${DEST_DIR}"
tarball="${DEST_DIR}/${asset}"

download_ok=0
if command -v gh >/dev/null 2>&1 && [ -n "${GH_TOKEN:-${GITHUB_TOKEN:-}}" ]; then
  # gh works for private cache repos too; --clobber keeps re-runs idempotent.
  if gh release download "${ALIGN_CPP_DEPS_TAG}" \
        --repo "${ALIGN_CPP_DEPS_REPO}" \
        --pattern "${asset}" \
        --dir "${DEST_DIR}" \
        --clobber >/dev/null 2>&1; then
    download_ok=1
  fi
fi

if [ "${download_ok}" -ne 1 ]; then
  # Public release asset: a plain HTTPS GET, no auth required.
  if curl -fsSL "${url}" -o "${tarball}"; then
    download_ok=1
  fi
fi

if [ "${download_ok}" -ne 1 ]; then
  log "no cached bundle found; build will compile dependencies from source."
  exit 0
fi

log "extracting ${tarball}"
tar -xzf "${tarball}" -C "${DEST_DIR}"

ilp_path="${DEST_DIR}/ilp"
superlu_path="${DEST_DIR}/superlu"

# Only export a path if its libraries are actually present, so a partial or
# unexpected bundle still degrades to a from-source build rather than a hard
# link error.
if compgen -G "${ilp_path}/lib/libILPSolverIf.a" >/dev/null; then
  echo "export ALIGN_ILP_PATH='${ilp_path}'"
  log "ALIGN_ILP_PATH=${ilp_path}"
else
  log "WARNING: bundle missing ilp/lib/libILPSolverIf.a; solvers will build from source."
fi

if compgen -G "${superlu_path}/lib/libsuperlu.a" >/dev/null; then
  echo "export ALIGN_SUPERLU_PATH='${superlu_path}'"
  log "ALIGN_SUPERLU_PATH=${superlu_path}"
else
  log "WARNING: bundle missing superlu/lib/libsuperlu.a; SuperLU will build from source."
fi

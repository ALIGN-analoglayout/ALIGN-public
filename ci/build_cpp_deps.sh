#!/usr/bin/env bash
#
# Producer side of ALIGN's C++ dependency binary cache.
#
# Harvests the COIN-OR/Cbc + SuperLU artifacts that a *from-source* ALIGN build
# just produced under _skbuild/, and packs them into the bundle layout consumed
# by ci/fetch_cpp_deps.sh:
#
#   <bundle>/ilp/lib/libILPSolverIf.a, libCbc.a, ...   (-> ALIGN_ILP_PATH)
#   <bundle>/ilp/include[/coin]/*.hpp                  COIN + ILPSolverIf headers
#   <bundle>/superlu/lib/libsuperlu.a [, libblas.a]    (-> ALIGN_SUPERLU_PATH)
#   <bundle>/superlu/include/*.h                        SuperLU headers
#
# This deliberately reuses whatever ALIGN's own CMake (ilpif.cmake /
# superlu.cmake) built, instead of re-implementing the solver build, so the
# bundle is byte-for-byte what a from-source build would have linked.
#
# Prerequisite: run a from-source build first with the cache DISABLED, e.g.
#   unset ALIGN_ILP_PATH ALIGN_SUPERLU_PATH
#   BUILD_TYPE=Release pip wheel . --no-deps -w /tmp/wheelhouse
#
# Usage:
#   ci/build_cpp_deps.sh [OUTPUT_TARBALL]
# Defaults OUTPUT_TARBALL to ./<asset-name>.tar.gz for the current platform.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
# shellcheck source=ci/cpp_deps_common.sh
source "${SCRIPT_DIR}/cpp_deps_common.sh"

OUT_TARBALL="${1:-${REPO_ROOT}/$(cpp_deps_asset_name)}"

log() { echo "[build_cpp_deps] $*" >&2; }
die() { log "ERROR: $*"; exit 1; }

# Locate the most recent scikit-build CMake build tree.
build_dir="$(find "${REPO_ROOT}/_skbuild" -type d -name 'cmake-build' 2>/dev/null | sort | tail -n1 || true)"
[ -n "${build_dir}" ] || die "no _skbuild/*/cmake-build found; run a from-source build first."
log "harvesting from ${build_dir}"

deps_dir="${build_dir}/_deps"

staging="$(mktemp -d)"
trap 'rm -rf "${staging}"' EXIT
mkdir -p "${staging}/ilp/lib" "${staging}/ilp/include/coin" \
         "${staging}/superlu/lib" "${staging}/superlu/include"

# --- COIN-OR / Cbc / SYMPHONY static libraries -----------------------------
ilp_libs=(
  libILPSolverIf.a libCbc.a libCbcSolver.a libClp.a libClpSolver.a libCgl.a
  libOsi.a libOsiClp.a libOsiCbc.a libCoinUtils.a libSym.a libOsiSym.a
)
missing=0
for lib in "${ilp_libs[@]}"; do
  found="$(find "${build_dir}" -type f -name "${lib}" 2>/dev/null | head -n1 || true)"
  if [ -n "${found}" ]; then
    cp -f "${found}" "${staging}/ilp/lib/"
    log "  + ilp/lib/${lib}"
  else
    log "  ! missing ${lib}"
    missing=$((missing + 1))
  fi
done
[ -f "${staging}/ilp/lib/libILPSolverIf.a" ] || die "libILPSolverIf.a not produced; aborting."

# COIN headers (over-inclusive on purpose: extra headers are harmless, while a
# missing one breaks the consumer build).  Place a flat copy in include/ and a
# coin/-prefixed copy in include/coin/ so both #include styles resolve.
if [ -d "${deps_dir}" ]; then
  # ILPSolverIf's own public headers.
  if [ -d "${deps_dir}/ilpsolverif-src/ILPSolverIf" ]; then
    find "${deps_dir}/ilpsolverif-src/ILPSolverIf" -maxdepth 1 \( -name '*.h' -o -name '*.hpp' \) \
      -exec cp -f {} "${staging}/ilp/include/" \;
  fi
  # COIN-OR headers, wherever the cbc build dropped them (install trees, src).
  while IFS= read -r hdr; do
    cp -f "${hdr}" "${staging}/ilp/include/" 2>/dev/null || true
    cp -f "${hdr}" "${staging}/ilp/include/coin/" 2>/dev/null || true
  done < <(find "${deps_dir}" -type f \( -name '*.hpp' -o -name '*.h' \) \
             \( -path '*Cbc*' -o -path '*Clp*' -o -path '*Cgl*' -o -path '*Osi*' \
                -o -path '*CoinUtils*' -o -path '*Sym*' -o -path '*coin*' -o -path '*Coin*' \) 2>/dev/null)
fi
ilp_hdr_count="$(find "${staging}/ilp/include" -type f | wc -l | tr -d ' ')"
log "  ilp headers: ${ilp_hdr_count}"

# --- SuperLU ---------------------------------------------------------------
for lib in libsuperlu.a libblas.a; do
  found="$(find "${build_dir}" -type f -name "${lib}" 2>/dev/null | head -n1 || true)"
  if [ -n "${found}" ]; then
    cp -f "${found}" "${staging}/superlu/lib/"
    log "  + superlu/lib/${lib}"
  elif [ "${lib}" = "libsuperlu.a" ]; then
    die "libsuperlu.a not produced; aborting."
  fi
done
if [ -d "${deps_dir}" ]; then
  find "${deps_dir}" -type f \( -name 'slu_*.h' -o -name 'superlu_*.h' -o -name 'supermatrix.h' \
       -o -name 'colamd.h' -o -name 'html_mainpage.h' \) \
    -exec cp -f {} "${staging}/superlu/include/" \; 2>/dev/null || true
fi
superlu_hdr_count="$(find "${staging}/superlu/include" -type f | wc -l | tr -d ' ')"
log "  superlu headers: ${superlu_hdr_count}"

# --- Manifest + pack -------------------------------------------------------
{
  echo "platform=$(cpp_deps_platform)"
  echo "signature=$(cpp_deps_signature)"
  echo "built=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "ilp_libs_missing=${missing}"
} > "${staging}/manifest.txt"

mkdir -p "$(dirname "${OUT_TARBALL}")"
tar -C "${staging}" -czf "${OUT_TARBALL}" ilp superlu manifest.txt
log "wrote ${OUT_TARBALL}"
echo "${OUT_TARBALL}"

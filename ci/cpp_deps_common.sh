# shellcheck shell=bash
#
# Shared helpers for ALIGN's C++ dependency binary cache.
#
# The COIN-OR / Cbc / SYMPHONY solver stack (pulled by ilpif.cmake) and SuperLU
# (pulled by superlu.cmake) are the only C++ dependencies that ALIGN compiles
# from source on every CI run.  To avoid recompiling them every time, prebuilt
# static-library bundles are published as GitHub Release assets in a dedicated
# cache repository and downloaded by ci/fetch_cpp_deps.sh.
#
# This file is meant to be `source`d; it only defines functions and the few
# overridable defaults below.  Both the producer (ci/build_cpp_deps.sh) and the
# consumer (ci/fetch_cpp_deps.sh) source it so the asset naming stays in sync.
#
# Overridable via environment:
#   ALIGN_CPP_DEPS_REPO      cache repository (owner/name) holding the releases
#   ALIGN_CPP_DEPS_TAG       release tag whose assets hold the bundles
#   ALIGN_CPP_DEPS_PLATFORM  platform key override (else auto-detected)

: "${ALIGN_CPP_DEPS_REPO:=ALIGN-analoglayout/ALIGN-public}"
: "${ALIGN_CPP_DEPS_TAG:=cpp-deps}"

# Capture this file's directory at *source* time, when BASH_SOURCE[0] is
# populated (it is not always available later from within a function).
_CPP_DEPS_COMMON_DIR="$(cd "$(dirname "${BASH_SOURCE[0]:-.}")" 2>/dev/null && pwd || echo "${PWD}")"

# Resolve the ALIGN repo root robustly, independent of the current directory or
# how this file was sourced: prefer `git rev-parse`, else walk up looking for the
# marker file every checkout has.
_cpp_deps_repo_root() {
  local d
  if d="$(git rev-parse --show-toplevel 2>/dev/null)" && \
     [ -f "${d}/PlaceRouteHierFlow/thirdparty/ilpif.cmake" ]; then
    echo "${d}"
    return
  fi
  for d in "${_CPP_DEPS_COMMON_DIR}" "${_CPP_DEPS_COMMON_DIR}/.." "${PWD}"; do
    d="$(cd "${d}" 2>/dev/null && pwd || true)"
    while [ -n "${d}" ] && [ "${d}" != "/" ]; do
      if [ -f "${d}/PlaceRouteHierFlow/thirdparty/ilpif.cmake" ]; then
        echo "${d}"
        return
      fi
      d="$(dirname "${d}")"
    done
  done
  echo "${PWD}"
}

# Platform key used to disambiguate bundles across OS/arch/libc.
#   - wheels (cibuildwheel) export AUDITWHEEL_PLAT on Linux -> use it directly
#   - macOS wheels -> macosx_<arch>
#   - the docker image build sets ALIGN_CPP_DEPS_PLATFORM=ubuntu-22.04-x86_64
cpp_deps_platform() {
  if [ -n "${ALIGN_CPP_DEPS_PLATFORM:-}" ]; then
    echo "${ALIGN_CPP_DEPS_PLATFORM}"
    return
  fi
  if [ -n "${AUDITWHEEL_PLAT:-}" ]; then
    echo "${AUDITWHEEL_PLAT}"
    return
  fi
  local arch
  arch="$(uname -m)"
  case "$(uname -s)" in
    Darwin) echo "macosx_${arch}" ;;
    Linux)  echo "linux_${arch}" ;;
    *)      echo "unknown_${arch}" ;;
  esac
}

# Extract the pinned upstream revision of a dependency from its .cmake file.
# Reads the first `GIT_TAG <value>` line, ignoring comments/whitespace.
_cpp_deps_git_tag() {
  local cmake_file="$1"
  awk '
    /^[[:space:]]*#/ { next }
    /GIT_TAG/ {
      for (i = 1; i <= NF; i++) {
        if ($i == "GIT_TAG") { print $(i+1); exit }
      }
    }' "$cmake_file"
}

# A short, stable signature of the *exact* dependency versions this checkout
# would build from source.  Bumping the ALIGN-public or SuperLU revision
# changes the signature, which transparently invalidates the binary cache (the
# new asset name simply won't exist yet, so CI rebuilds and republishes it).
cpp_deps_signature() {
  local root ilp_tag superlu_tag combined
  root="$(_cpp_deps_repo_root)"
  ilp_tag="$(_cpp_deps_git_tag "${root}/PlaceRouteHierFlow/thirdparty/ilpif.cmake")"
  superlu_tag="$(_cpp_deps_git_tag "${root}/PlaceRouteHierFlow/thirdparty/superlu.cmake")"
  combined="ilp=${ilp_tag};superlu=${superlu_tag}"
  # sha256 first 12 hex chars; tolerate either shasum (macOS) or sha256sum (Linux)
  if command -v sha256sum >/dev/null 2>&1; then
    printf '%s' "${combined}" | sha256sum | cut -c1-12
  else
    printf '%s' "${combined}" | shasum -a 256 | cut -c1-12
  fi
}

# Canonical asset filename for a (signature, platform) pair.
cpp_deps_asset_name() {
  echo "cpp-deps-$(cpp_deps_signature)-$(cpp_deps_platform).tar.gz"
}

# Public download URL for the current asset in the cache repo's release.
cpp_deps_asset_url() {
  echo "https://github.com/${ALIGN_CPP_DEPS_REPO}/releases/download/${ALIGN_CPP_DEPS_TAG}/$(cpp_deps_asset_name)"
}

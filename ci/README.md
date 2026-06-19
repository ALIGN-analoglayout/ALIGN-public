c
          ALIGN_CPP_DEPS_TAG# ALIGN C++ Dependency Cache

ALIGN's C++ build compiles two heavy dependencies from source — the
COIN-OR/Cbc/SYMPHONY solver stack (via `ALIGN-public`) and SuperLU — on
every CI run.  This directory implements a binary cache that pre-builds those
artifacts once and stores them as GitHub Release assets in a separate
repository, so wheel and Docker builds can download and skip the compile.

## Cache repository

**`ALIGN-analoglayout/ALIGN-public`** holds a single, mutable release tagged
`cpp-deps`.  Each asset in that release is a `.tar.gz` bundle for a specific
combination of dependency versions and target platform.

## Asset naming and the dependency signature

Every asset is named:

```
cpp-deps-<signature>-<platform>.tar.gz
```

* **`<signature>`** — a 12-character SHA-256 prefix computed from the exact
  pinned revisions in `ilpif.cmake` (`GIT_TAG`) and `superlu.cmake`
  (`GIT_TAG`).  Bumping either of those tags changes the signature, so the old
  asset is simply ignored and CI rebuilds from source (and republishes the new
  bundle).

* **`<platform>`** — one of:
  | Value | Used by |
  |---|---|
  | `manylinux_2_28_x86_64` | Linux wheel builds (cibuildwheel) |
  | `macosx_arm64` | macOS arm64 wheel builds |
  | `ubuntu-22.04-x86_64` | Docker image build |

These are computed automatically by `ci/cpp_deps_common.sh`.

## Bundle layout

```
<bundle>/
  ilp/
    lib/        libILPSolverIf.a  libCbc.a  libCbcSolver.a  libClp.a ...
    include/    ILPSolverIf.hpp  (COIN headers, flat)
    include/coin/               (same headers, coin/-prefixed)
  superlu/
    lib/        libsuperlu.a  [libblas.a]
    include/    slu_*.h  superlu_*.h ...
  manifest.txt
```

CMake consumes the bundle via two env vars:

| Env var | cmake file | Effect |
|---|---|---|
| `ALIGN_ILP_PATH` | `ilpif.cmake` | imports prebuilt solver static libs |
| `ALIGN_SUPERLU_PATH` | `superlu.cmake` | imports prebuilt SuperLU |

Both are set to fixed paths (`/tmp/align-cpp-deps/ilp` and
`/tmp/align-cpp-deps/superlu`) by the `before-all` / ENV directives in
`pyproject.toml` and `docker/dockerfile`.  If the files are absent (cache
miss), CMake's `find_library` silently falls back to the from-source build.

## Scripts

| Script | Role |
|---|---|
| `ci/cpp_deps_common.sh` | Shared helpers: platform detection, signature, asset name/URL.  `source` it from other scripts. |
| `ci/fetch_cpp_deps.sh [DEST]` | Consumer: downloads + extracts the bundle for the current platform.  Exits 0 on cache miss.  Logs to stderr. |
| `ci/build_cpp_deps.sh [OUT]` | Producer: harvests artifacts from a completed `_skbuild/` tree and packs them into the bundle tarball. |

## Producer workflow

`.github/workflows/build-cpp-deps.yml` runs automatically whenever
`ilpif.cmake` or `superlu.cmake` changes (and on `workflow_dispatch`).  It:

1. Builds ALIGN from source (with `ALIGN_ILP_PATH`/`ALIGN_SUPERLU_PATH`
   unset) on each matrix platform.
2. Runs `ci/build_cpp_deps.sh` to harvest the artifacts.
3. Uploads the tarball to the `ALIGN-analoglayout/ALIGN-public` release.

**Required secret**: `CPP_DEPS_CACHE_TOKEN` — a GitHub PAT with `Contents:
write` permission on `ALIGN-analoglayout/ALIGN-public`.

## How to force a rebuild

Trigger `build-cpp-deps.yml` manually via `workflow_dispatch`, or bump a
`GIT_TAG` in `ilpif.cmake` or `superlu.cmake` (which changes the signature and
the asset name, so the next wheel/Docker build falls back to source and the
producer workflow republishes).

# Release Benchmark Metrics System — Design Spec

**Date:** 2026-06-17
**Branch:** feat/release-benchmarks
**Status:** Approved

---

## Goal

Automatically collect layout quality and post-layout simulation metrics after every PyPI release of `align-analoglayout`, and publish a trend dashboard to GitHub Pages so regressions are visible across releases.

---

## Architecture

```
PyPI publish completes (v*.*.* tag on master)
        │
        ▼
benchmark.yml  (triggered via workflow_run on "Build and Publish Wheels")
        │
        ├── benchmark matrix (6 circuits × parallel)
        │     each job:
        │       1. restore Magic + ngspice from cache (key: magic-<ver>-ubuntu)
        │          └── cache miss: build Magic from source (~8 min), then cache
        │       2. pip install align-analoglayout==<released version>
        │       3. run ALIGN → GDS + LEF
        │       4. Magic extraction → extracted SPICE netlist
        │       5. ngspice simulation → metrics JSON
        │       6. upload artifact
        │
        └── aggregate-and-publish job (needs all matrix jobs)
              1. download all artifacts
              2. merge into single results.json
              3. load history.json from gh-pages branch
              4. append this release, detect regressions (>10% change)
              5. render static HTML dashboard (Chart.js via CDN)
              6. push to gh-pages branch → GitHub Pages
```

---

## Trigger

```yaml
on:
  workflow_run:
    workflows: ["Build and Publish Wheels"]
    types: [completed]
    branches: [master]
```

Only fires when the publish workflow **succeeds** — skips failed or cancelled runs.

---

## Benchmark Circuit Set

Six representative circuits from `examples/`, covering a range of complexity, all compatible with `FinFET14nm_Mock_PDK`:

| Circuit | Type | Complexity |
|---|---|---|
| `buffer` | Digital buffer | Tiny |
| `five_transistor_ota` | OTA | Small |
| `current_mirror_ota` | OTA | Small-medium |
| `high_speed_comparator` | Comparator | Medium |
| `variable_gain_amplifier` | Amplifier | Medium-large |
| `switched_capacitor_filter` | Filter | Large |

PDK: `FinFET14nm_Mock_PDK` only (single PDK keeps runtime bounded; additional PDKs can be added later).

---

## Metrics

### Layout Quality (from LEF/GDS output)

| Metric | Source |
|---|---|
| Total cell area (µm²) | LEF MACRO bounding box |
| Total wirelength (µm) | Sum of all net segment lengths from DEF/LEF |
| Total via count | Count of via instances in DEF |
| ALIGN runtime (s) | Wall clock of ALIGN invocation |

### Post-Layout Simulation (ngspice on Magic-extracted netlist)

| Circuit | Metrics |
|---|---|
| `buffer` | Propagation delay tpHL (ns), tpLH (ns) |
| `five_transistor_ota` | DC gain (dB), unity-gain bandwidth (MHz), phase margin (°) |
| `current_mirror_ota` | DC gain (dB), CMRR (dB), bandwidth (MHz) |
| `high_speed_comparator` | Regeneration time (ns), static power (µW) |
| `variable_gain_amplifier` | Gain range (dB), bandwidth (MHz) |
| `switched_capacitor_filter` | -3dB frequency (MHz), passband ripple (dB) |

Simulation uses testbench netlists stored in `benchmarks/testbenches/<circuit>/tb.sp`.

---

## Magic Tech Files

ALIGN's mock PDKs have no existing Magic tech files. Stub tech files are created at:

```
benchmarks/magic_tech/FinFET14nm_Mock_PDK/
  FinFET14nm.tech       ← layer definitions, minimal DRC rules
  FinFET14nm.magicrc    ← startup file referencing the tech
  ext2spice.tcl         ← extraction script
```

Stub RC values (consistent with 14nm-class ballpark; physically approximate but stable across releases):

| Layer | Sheet R (Ω/sq) | Area Cap (aF/µm²) |
|---|---|---|
| M1 | 0.12 | 35 |
| M2 | 0.10 | 28 |
| M3–M5 | 0.08 | 22 |
| Via (each) | 5 Ω flat | — |

These values are fixed in the repo — they don't change unless intentionally bumped. This ensures that parasitic changes in the dashboard reflect layout changes, not tooling changes.

---

## Tool Versions & Caching

| Tool | Version | Install method | Cache key |
|---|---|---|---|
| Magic | 7.3.x (latest stable) | Build from source | `magic-<version>-<os>` |
| ngspice | 43 | `apt install ngspice` | apt cache path |

Cache stored via `actions/cache`. On cache miss (~8 min for Magic build), subsequent runs hit the cache (~30 s). Cache is invalidated only when tool version strings change in the workflow.

---

## GitHub Actions Jobs

| Job | Runner | Est. wall clock |
|---|---|---|
| `benchmark` (6× parallel) | ubuntu-latest | 5–15 min (tools cached: +30 s / cold: +8 min) |
| `aggregate-and-publish` | ubuntu-latest | ~2 min |

**Total per release:** ~15–20 min wall clock (parallel matrix).
**Cost:** Free — ALIGN-public is a public repo (unlimited GitHub Actions minutes).

---

## GitHub Pages Dashboard

**URL:** `https://align-analoglayout.github.io/ALIGN-public/benchmarks/`

**Layout:**
- Version selector dropdown (all tagged releases)
- Two tabs: **Layout Quality** | **Simulation**
- Layout Quality tab: bar charts per circuit (area, wirelength, via count, runtime); previous 5 releases overlaid as lines
- Simulation tab: per-circuit cards with each metric and a sparkline trend across last 10 releases
- Summary regression table: flag any metric that changed >10% vs previous release

**Data on `gh-pages` branch:**

```
benchmarks/
  index.html          ← regenerated on every release
  history.json        ← append-only array of all release results
  v0.9.8/
    results.json      ← raw metrics for that release
  v0.9.9/
    results.json
  ...
```

`history.json` is the source of truth for the dashboard. `results.json` per version is kept for raw data access.

---

## Regression Detection

The aggregate job compares each metric against the previous release:
- **>10% degradation** → warning logged, summary table highlights red
- **>25% degradation** → workflow exits with failure (blocks attention, does not block future releases)

Thresholds are configurable via a `benchmarks/config.json` file in the repo.

---

## File Layout in Repo

```
benchmarks/
  config.json                         ← regression thresholds, tool versions
  magic_tech/
    FinFET14nm_Mock_PDK/
      FinFET14nm.tech
      FinFET14nm.magicrc
      ext2spice.tcl
  testbenches/
    buffer/tb.sp
    five_transistor_ota/tb.sp
    current_mirror_ota/tb.sp
    high_speed_comparator/tb.sp
    variable_gain_amplifier/tb.sp
    switched_capacitor_filter/tb.sp
  scripts/
    run_align.sh                       ← wrapper: run ALIGN, extract layout metrics
    run_extraction.sh                  ← wrapper: Magic extraction
    run_simulation.sh                  ← wrapper: ngspice simulation
    aggregate.py                       ← merge artifacts, update history.json
    render_dashboard.py                ← generate index.html from history.json

.github/workflows/
  benchmark.yml                        ← the benchmark workflow
```

---

## Out of Scope (explicit non-goals)

- Parasitic extraction for Bulk45nm/Bulk65nm PDKs (can be added later)
- Commercial simulator support (Spectre, HSPICE)
- LVS checking (separate concern)
- PR-level benchmarking (only on tagged releases)
- Self-hosted runners (free-tier ubuntu-latest is sufficient)

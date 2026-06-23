#!/usr/bin/env python3
"""
aggregate.py <artifacts_dir> <history_json> <version> <config_json>

artifacts_dir: directory containing metrics.json files (searched recursively)
history_json:  path to history.json on gh-pages branch (created if absent)
version:       release tag string, e.g. "v0.9.8"
config_json:   path to benchmarks/config.json
"""
import json, sys, glob, pathlib

def load_artifacts(artifacts_dir):
    results = {}
    for f in glob.glob(f"{artifacts_dir}/**/metrics.json", recursive=True):
        try:
            with open(f) as fp:
                data = json.load(fp)
        except (json.JSONDecodeError, IOError) as e:
            print(f"WARNING: failed to load {f}: {e}", file=sys.stderr)
            continue
        circuit = data.get('circuit')
        pdk = data.get('pdk', 'unknown')
        if circuit:
            results[f"{circuit}|{pdk}"] = data
    return results

def check_regressions(current, previous, thresholds):
    """Compare current vs previous release. Higher = worse for all metrics."""
    warn_pct = thresholds['warning_pct']
    fail_pct = thresholds['failure_pct']
    warnings, failures = [], []

    # Keys that are non-deterministic on shared CI runners and must not gate CI
    skip_keys = {'circuit', 'version', 'timestamp', 'runtime_s', 'pdk'}

    for circuit, metrics in current.items():
        if circuit not in previous:
            continue
        prev = previous[circuit]
        for key, val in metrics.items():
            if key in skip_keys:
                continue
            if not isinstance(val, (int, float)):
                continue
            prev_val = prev.get(key)
            if not isinstance(prev_val, (int, float)) or prev_val <= 0:
                continue
            pct = (val - prev_val) / prev_val * 100
            entry = {'circuit': circuit, 'metric': key,
                     'current': val, 'previous': prev_val,
                     'pct_change': round(pct, 2)}
            if pct > fail_pct:
                failures.append(entry)
            elif pct > warn_pct:
                warnings.append(entry)

    return warnings, failures

def main():
    if len(sys.argv) != 5:
        print("Usage: aggregate.py <artifacts_dir> <history_json> <version> <config_json>")
        sys.exit(1)

    artifacts_dir, history_file, version, config_file = sys.argv[1:]

    try:
        with open(config_file) as f:
            config = json.load(f)
    except FileNotFoundError:
        print(f"ERROR: config file not found: {config_file}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"ERROR: config file is not valid JSON: {e}", file=sys.stderr)
        sys.exit(1)

    current = load_artifacts(artifacts_dir)
    if not current:
        print(f"ERROR: no metrics.json files found in {artifacts_dir}", file=sys.stderr)
        sys.exit(1)

    history = []
    history_path = pathlib.Path(history_file)
    history_path.parent.mkdir(parents=True, exist_ok=True)
    if history_path.exists():
        try:
            with open(history_path) as f:
                history = json.load(f)
        except (json.JSONDecodeError, IOError) as e:
            print(f"ERROR: failed to load history file {history_file}: {e}", file=sys.stderr)
            sys.exit(1)

    previous = {}
    if history:
        for c in history[-1].get('circuits', []):
            key = f"{c['circuit']}|{c.get('pdk', 'unknown')}"
            previous[key] = c

    warnings, failures = check_regressions(current, previous, config['regression_thresholds'])

    release = {
        'version': version,
        'circuits': list(current.values()),
        'regressions': {'warnings': warnings, 'failures': failures}
    }
    history.append(release)

    with open(history_path, 'w') as f:
        json.dump(history, f, indent=2)

    version_dir = history_path.parent / version
    version_dir.mkdir(parents=True, exist_ok=True)
    with open(version_dir / 'results.json', 'w') as f:
        json.dump(release, f, indent=2)

    print(f"Aggregated {len(current)} circuits for {version}")
    if warnings:
        print(f"WARNINGS ({len(warnings)}): {json.dumps(warnings)}")
    if failures:
        print(f"FAILURES ({len(failures)}): {json.dumps(failures)}", file=sys.stderr)
        sys.exit(1)

if __name__ == '__main__':
    main()

#!/bin/bash

(cd ../Intel; python generate_comparator.py)

pytest --run_intel_22nm -- tests/test_comparator.py

cp INPUT/comparator_dr_globalrouting.json ../../Viewer/INPUT/

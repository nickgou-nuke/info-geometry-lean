#!/usr/bin/env bash
# run_evidence.sh
# Runs all executable proof evidence scripts in the workspace.

set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
cd "$DIR"

echo "============================================================"
echo "RUNNING ALL CAPSTONE PROOF EVIDENCE SCHEMES"
echo "============================================================"

echo ""
python3 sympy_fenchel_madelung.py

echo ""
sage sage_metriplectic.sage

echo ""
python3 galgebra_rotor.py

echo ""
# Run GAP in quiet mode with stdin redirected to EOF so it does not hang
gap -q -b gap_lie_tracefree.g < /dev/null

echo ""
echo "============================================================"
echo "ALL PROOF EVIDENCE RUNS COMPLETED SUCCESSFULLY"
echo "============================================================"

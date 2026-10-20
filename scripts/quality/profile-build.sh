#!/bin/bash
# Profile Lean 4 build times per file using lake and lean --profile

set -e

LOG=profile-build-$(date +%Y%m%d-%H%M%S).log

# Build changed owner modules incrementally with profiling enabled.  The
# repository build cache is intentionally preserved; use an explicit owner
# target when profiling a dependency or umbrella target.
L4_PROFILE=1 python3 tools/infra/build_changed_lean.py --wait-for-build-lock 2>&1 | tee "$LOG"

echo "\nBuild log with timing saved to $LOG"
echo "To analyze slowest files, search for '[profile]' and 'elapsed' in the log."

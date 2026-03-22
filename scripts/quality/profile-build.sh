#!/bin/bash
# Profile Lean 4 build times per file using lake and lean --profile

set -e

LOG=profile-build-$(date +%Y%m%d-%H%M%S).log

# Clean previous build
lake clean

# Build with verbose output and profile enabled
L4_PROFILE=1 python3 tools/run_locked_lake_build.py -v 2>&1 | tee "$LOG"

echo "\nBuild log with timing saved to $LOG"
echo "To analyze slowest files, search for '[profile]' and 'elapsed' in the log."

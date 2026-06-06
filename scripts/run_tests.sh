#!/usr/bin/env bash
set -euo pipefail

echo "[run-tests] running Lean test suite"
lake test

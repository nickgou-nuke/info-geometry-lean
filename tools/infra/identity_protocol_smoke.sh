#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

# Shell syntax checks via sandbox when possible, with safe fallback when bwrap is unavailable.
tools/infra/bwrap_preflight.sh -- bash -n tools/infra/hive_with_env.sh
tools/infra/bwrap_preflight.sh -- bash -n tools/infra/identity_protocol_smoke.sh

python3 -m py_compile \
  tools/infra/identity_protocol_metrics.py \
  tools/infra/identity_protocol_runner.py \
  tools/infra/hive_qi_heartbeat.py \
  tools/infra/hive_arango_queue.py

python3 tools/infra/identity_protocol_runner.py --episodes 5 --print-summary

echo "identity protocol smoke: PASS"

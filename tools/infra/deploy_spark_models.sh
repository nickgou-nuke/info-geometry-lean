#!/usr/bin/env bash
set -euo pipefail

# REFINED DGX SPARK OPERATIONAL RECIPE
# Deployment script for asymmetric Lean 4 Proof-Orchestration backends.
# Uses bare-metal vLLM logic for high-precision resource management.

need_cmd() {
  command -v "$1" >/dev/null 2>&1 || {
    echo "Missing required command: $1" >&2
    exit 1
  }
}

need_cmd python3
need_cmd curl

PROPOSER_MODEL="${PROPOSER_MODEL:-Qwen/Qwen3.6-35B-A3B-FP8}"
FORMALIZER_MODEL="${FORMALIZER_MODEL:-deepseek-ai/DeepSeek-Prover-V2-7B}"
PROPOSER_PORT="${PROPOSER_PORT:-18789}"
FORMALIZER_PORT="${FORMALIZER_PORT:-8001}"
PROPOSER_SERVED_NAME="${PROPOSER_SERVED_NAME:-qwen3-proposer}"
FORMALIZER_SERVED_NAME="${FORMALIZER_SERVED_NAME:-deepseek-formalizer}"

# Note: context and memory limits are tuned for stable low-latency proof sessions.
PROPOSER_LIMIT="${PROPOSER_LIMIT:---gpu-memory-utilization 0.45 --max-model-len 16384}"
FORMALIZER_LIMIT="${FORMALIZER_LIMIT:---gpu-memory-utilization 0.20 --max-model-len 24576}"

STARTUP_TIMEOUT_SEC="${STARTUP_TIMEOUT_SEC:-900}"
STARTUP_POLL_SEC="${STARTUP_POLL_SEC:-5}"
PROPOSER_URL="${PROPOSER_URL:-http://127.0.0.1:${PROPOSER_PORT}/v1/models}"
FORMALIZER_URL="${FORMALIZER_URL:-http://127.0.0.1:${FORMALIZER_PORT}/v1/models}"

SERVER_LOG_DIR="${SERVER_LOG_DIR:-logs/vllm}"
RUN_ID="${RUN_ID:-$(date -u +%Y%m%dT%H%M%SZ)}"
mkdir -p "$SERVER_LOG_DIR"

probe_url() {
  local url="$1"
  curl -fsS "$url" >/dev/null 2>&1
}

wait_for_url() {
  local label="$1"
  local url="$2"
  local start_ts="$3"
  local timeout="$4"
  local poll="$5"
  printf "Waiting for %s (%s)...\n" "$label" "$url"
  while ! probe_url "$url"; do
    local now
    now="$(date +%s)"
    if [ $((now - start_ts)) -ge "$timeout" ]; then
      printf "ERROR: timeout while waiting for %s (%s)\n" "$label" "$url" >&2
      return 1
    fi
    sleep "$poll"
  done
  printf "%s is ACTIVE.\n" "$label"
}

launch_server() {
  local label="$1"
  local model="$2"
  local port="$3"
  local served_name="$4"
  local limit_flags="$5"
  local log_file="$6"
  local pid_file="$7"

  local -a limit_args=()
  if [ -n "$limit_flags" ]; then
    read -r -a limit_args <<< "$limit_flags"
  fi

  printf "Launching %s on port %s...\n" "$label" "$port"
  python3 -m vllm.entrypoints.openai.api_server \
    --model "$model" \
    --port "$port" \
    "${limit_args[@]}" \
    --served-model-name "$served_name" \
    >"$log_file" 2>&1 &

  local pid=$!
  printf "%s\n" "$pid" >"$pid_file"
  printf "%s PID: %s (log: %s)\n" "$label" "$pid" "$log_file"
}

echo "--- [STAGGERED BOOT] Initializing DGX Spark Core ---"

START_TS="$(date +%s)"
PROPOSER_LOG="$SERVER_LOG_DIR/${RUN_ID}_proposer.log"
FORMALIZER_LOG="$SERVER_LOG_DIR/${RUN_ID}_formalizer.log"
PROPOSER_PID_FILE="$SERVER_LOG_DIR/${RUN_ID}_proposer.pid"
FORMALIZER_PID_FILE="$SERVER_LOG_DIR/${RUN_ID}_formalizer.pid"

if probe_url "$PROPOSER_URL"; then
  echo "Proposer already active at $PROPOSER_URL; skipping launch."
else
  launch_server "Proposer" "$PROPOSER_MODEL" "$PROPOSER_PORT" "$PROPOSER_SERVED_NAME" "$PROPOSER_LIMIT" "$PROPOSER_LOG" "$PROPOSER_PID_FILE"
fi
wait_for_url "Proposer" "$PROPOSER_URL" "$START_TS" "$STARTUP_TIMEOUT_SEC" "$STARTUP_POLL_SEC"

if probe_url "$FORMALIZER_URL"; then
  echo "Formalizer already active at $FORMALIZER_URL; skipping launch."
else
  launch_server "Formalizer" "$FORMALIZER_MODEL" "$FORMALIZER_PORT" "$FORMALIZER_SERVED_NAME" "$FORMALIZER_LIMIT" "$FORMALIZER_LOG" "$FORMALIZER_PID_FILE"
fi
wait_for_url "Formalizer" "$FORMALIZER_URL" "$START_TS" "$STARTUP_TIMEOUT_SEC" "$STARTUP_POLL_SEC"

echo "--- [SUCCESS] Spire Proof Backends are synchronized ---"
echo "Proposer    : $PROPOSER_URL"
echo "Formalizer  : $FORMALIZER_URL"
echo "Run ID      : $RUN_ID"
echo "Log dir     : $SERVER_LOG_DIR"

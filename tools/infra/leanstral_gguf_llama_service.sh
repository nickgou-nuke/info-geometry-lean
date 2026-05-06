#!/usr/bin/env bash
set -euo pipefail

# Leanstral GGUF resident service for DGX Spark / GB10 via llama.cpp.
#
# This is the quantized Leanstral path. It serves jackcloudman's GGUF
# quantization of mistralai/Leanstral-2603 through llama-server's OpenAI-style
# HTTP API.  It is a proposal engine only; Lean/Hive gates remain proof
# authority.

LLAMA_SERVER_BIN="${LLAMA_SERVER_BIN:-llama-server}"
HOST="${LEANSTRAL_GGUF_HOST:-0.0.0.0}"
PORT="${LEANSTRAL_GGUF_PORT:-18789}"
SERVED_MODEL_NAME="${LEANSTRAL_GGUF_SERVED_MODEL_NAME:-leanstral-gguf}"
CTX_SIZE="${LEANSTRAL_GGUF_CTX_SIZE:-128000}"
GPU_LAYERS="${LEANSTRAL_GGUF_GPU_LAYERS:--1}"
THREADS="${LEANSTRAL_GGUF_THREADS:-0}"
PARALLEL="${LEANSTRAL_GGUF_PARALLEL:-1}"
FLASH_ATTN="${LEANSTRAL_GGUF_FLASH_ATTN:-1}"
FIT="${LEANSTRAL_GGUF_FIT:-on}"
MODEL_PATH="${LEANSTRAL_GGUF_MODEL:-/home/goutev/models/Leanstral-2603-GGUF/mistralai_Leanstral-128x3.9B-2603-Q4_K_M.gguf}"
CHAT_TEMPLATE="${LEANSTRAL_GGUF_CHAT_TEMPLATE:-/home/goutev/models/Leanstral-2603-GGUF/chat_template.jinja}"

if [[ ! -f "$MODEL_PATH" ]]; then
  cat >&2 <<EOF
Missing Leanstral GGUF model file:
  $MODEL_PATH

Download it with, for example:
  mkdir -p /home/goutev/models/Leanstral-2603-GGUF
  hf download jackcloudman/Leanstral-2603-GGUF \
    mistralai_Leanstral-128x3.9B-2603-Q4_K_M.gguf \
    --local-dir /home/goutev/models/Leanstral-2603-GGUF

If needed, export HF_TOKEN/HUGGING_FACE_HUB_TOKEN in your shell or systemd
environment file. Do not commit tokens into this repo.
EOF
  exit 64
fi

args=(
  -m "$MODEL_PATH"
  --host "$HOST"
  --port "$PORT"
  --alias "$SERVED_MODEL_NAME"
  --ctx-size "$CTX_SIZE"
  --parallel "$PARALLEL"
  -ngl "$GPU_LAYERS"
)

if [[ "$THREADS" != "0" ]]; then
  args+=(--threads "$THREADS")
fi

if [[ "$FLASH_ATTN" == "1" ]]; then
  args+=(-fa on)
fi

if [[ -n "$FIT" ]]; then
  args+=(-fit "$FIT")
fi

if [[ -f "$CHAT_TEMPLATE" ]]; then
  args+=(--jinja --chat-template-file "$CHAT_TEMPLATE")
else
  args+=(--jinja)
  cat >&2 <<EOF
Warning: chat template file not found:
  $CHAT_TEMPLATE
Continuing with --jinja only. For Leanstral reasoning blocks, download the
original/template-compatible chat_template.jinja and set LEANSTRAL_GGUF_CHAT_TEMPLATE.
EOF
fi

exec "$LLAMA_SERVER_BIN" "${args[@]}"

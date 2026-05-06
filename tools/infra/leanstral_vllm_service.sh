#!/usr/bin/env bash
set -euo pipefail

# Quantized Mistral-family resident vLLM service for DGX Spark / GB10.
#
# This script intentionally does not hardcode HF_TOKEN. If Hugging Face auth is
# required, provide it through the user environment or a systemd EnvironmentFile.
#
# Unquantized Leanstral-2603 is not the safe single-Spark resident default yet.
# Until an official Leanstral NVFP4 checkpoint exists, this launcher defaults to
# the official Mistral Small 4 NVFP4 checkpoint from the same 119B/6.5B-active
# Mistral 4 family.  It is a proposal engine only; Lean/Hive gates remain proof
# authority.

MODEL="${LEANSTRAL_MODEL:-${MISTRAL_RESIDENT_MODEL:-mistralai/Mistral-Small-4-119B-2603-NVFP4}}"
HOST="${LEANSTRAL_HOST:-0.0.0.0}"
PORT="${LEANSTRAL_PORT:-18789}"
MAX_MODEL_LEN="${LEANSTRAL_MAX_MODEL_LEN:-32768}"
MAX_NUM_SEQS="${LEANSTRAL_MAX_NUM_SEQS:-1}"
MAX_BATCHED_TOKENS="${LEANSTRAL_MAX_NUM_BATCHED_TOKENS:-8192}"
GPU_MEMORY_UTILIZATION="${LEANSTRAL_GPU_MEMORY_UTILIZATION:-0.75}"
KV_CACHE_DTYPE="${LEANSTRAL_KV_CACHE_DTYPE:-fp8}"
ATTENTION_BACKEND="${LEANSTRAL_ATTENTION_BACKEND:-TRITON_MLA}"
SERVED_MODEL_NAME="${LEANSTRAL_SERVED_MODEL_NAME:-mistral-small-4-nvfp4}"
QUANTIZATION="${LEANSTRAL_QUANTIZATION:-}"
CUDA_GRAPH_CAPTURE_SIZES="${LEANSTRAL_CUDAGRAPH_CAPTURE_SIZES:-1 2 4 8 16 32 64 128 256}"
MAX_CUDAGRAPH_CAPTURE_SIZE="${LEANSTRAL_MAX_CUDAGRAPH_CAPTURE_SIZE:-256}"
DISABLE_FLASHINFER_AUTOTUNE="${LEANSTRAL_DISABLE_FLASHINFER_AUTOTUNE:-1}"
TORCH_CUDA_ARCH_LIST_VALUE="${TORCH_CUDA_ARCH_LIST:-12.1a}"
TRITON_PTXAS_PATH_VALUE="${TRITON_PTXAS_PATH:-/usr/local/cuda/bin/ptxas}"
VLLM_SKIP_P2P_CHECK_VALUE="${VLLM_SKIP_P2P_CHECK:-1}"
VLLM_BIN="${VLLM_BIN:-vllm}"

export HF_HOME="${HF_HOME:-/home/goutev/.cache/huggingface_user}"
export VLLM_USE_DEEP_GEMM="${VLLM_USE_DEEP_GEMM:-1}"
export VLLM_ATTENTION_BACKEND="${VLLM_ATTENTION_BACKEND:-$ATTENTION_BACKEND}"
export VLLM_NO_FLASHINFER_AUTOTUNE="${VLLM_NO_FLASHINFER_AUTOTUNE:-$DISABLE_FLASHINFER_AUTOTUNE}"
export TORCH_CUDA_ARCH_LIST="$TORCH_CUDA_ARCH_LIST_VALUE"
export TRITON_PTXAS_PATH="$TRITON_PTXAS_PATH_VALUE"
export VLLM_SKIP_P2P_CHECK="$VLLM_SKIP_P2P_CHECK_VALUE"
export FLASHINFER_JIT_LOG_LEVEL="${FLASHINFER_JIT_LOG_LEVEL:-ERROR}"
export TRANSFORMERS_VERBOSITY="${TRANSFORMERS_VERBOSITY:-error}"
mkdir -p "$HF_HOME"

args=(
  serve "$MODEL"
  --host "$HOST"
  --port "$PORT"
  --served-model-name "$SERVED_MODEL_NAME"
  --max-model-len "$MAX_MODEL_LEN"
  --max-num-seqs "$MAX_NUM_SEQS"
  --max-num-batched-tokens "$MAX_BATCHED_TOKENS"
  --gpu-memory-utilization "$GPU_MEMORY_UTILIZATION"
  --kv-cache-dtype "$KV_CACHE_DTYPE"
  --attention-backend "$ATTENTION_BACKEND"
  --tool-call-parser mistral
  --enable-auto-tool-choice
  --reasoning-parser mistral
  --max-cudagraph-capture-size "$MAX_CUDAGRAPH_CAPTURE_SIZE"
)

if [[ -n "$QUANTIZATION" ]]; then
  args+=(--quantization "$QUANTIZATION")
fi

if [[ "$DISABLE_FLASHINFER_AUTOTUNE" == "1" ]]; then
  args+=(--no-enable-flashinfer-autotune)
fi

if [[ -n "$CUDA_GRAPH_CAPTURE_SIZES" ]]; then
  # shellcheck disable=SC2206
  capture_sizes=($CUDA_GRAPH_CAPTURE_SIZES)
  args+=(--cudagraph-capture-sizes "${capture_sizes[@]}")
fi

exec "$VLLM_BIN" "${args[@]}"

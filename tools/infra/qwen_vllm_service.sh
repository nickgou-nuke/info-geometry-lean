#!/usr/bin/env bash
# ⚖️ QWEN 35B RESIDENT SERVICE
# Hardware: Grace Blackwell (GB10) - 121GB VRAM
# Optimization: Using FlashInfer backend and FP8 KV Cache for Blackwell SM121.
# MoE: Enabling DeepGEMM via environment variable for optimal expert dispatch.

export HF_TOKEN="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"
export HF_HOME="/home/goutev/.cache/huggingface_user"
export VLLM_USE_DEEP_GEMM=1

# Note: using -o for passthrough vLLM options and --tp 1 for single-GPU Blackwell.
sparkrun run @eugr/qwen3.5-35b-a3b-fp8 \
    --tp 1 \
    --port 18789 \
    --label "service=qwen-vllm" \
    --gpu-mem 0.80 \
    --max-model-len 131072 \
    -o attention_backend=flashinfer \
    -o kv_cache_dtype=fp8 \
    -o enable_chunked_prefill=True \
    --ensure



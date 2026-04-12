#!/bin/bash

# REFINED DGX SPARK OPERATIONAL RECIPE
# Deployment script for asymmetric Lean 4 Proof-Orchestration backends.
# Uses bare-metal vLLM logic for high-precision resource management.

# 1. Models and Ports
PROPOSER_MODEL="Qwen/Qwen3-32B-FP8"
FORMALIZER_MODEL="deepseek-ai/DeepSeek-Prover-V2-7B"

# 2. Constraints (Refined for DGX Spark Blackwell)
# Note: Context and Memory limits are tuned for stable, low-latency proof sessions.
PROPOSER_LIMIT="--gpu-memory-utilization 0.45 --max-model-len 16384"
FORMALIZER_LIMIT="--gpu-memory-utilization 0.20 --max-model-len 24576"

echo "--- [STAGGERED BOOT] Initializing DGX Spark Core ---"

# 3. Phase 1: Proposer (Qwen3-32B)
echo "Launching Proposer on Port 8000..."
python3 -m vllm.entrypoints.openai.api_server \
    --model $PROPOSER_MODEL \
    --port 8000 \
    $PROPOSER_LIMIT \
    --served-model-name "qwen3-proposer" &

# Wait for Proposer to heartbeat
echo "Waiting for Proposer to stabilize (heartbeat at :8000)..."
until curl -s http://localhost:8000/v1/models > /dev/null; do
    sleep 5
done
echo "Proposer is ACTIVE."

# 4. Phase 2: Formalizer (DeepSeek-Prover-V2-7B)
echo "Launching Formalizer on Port 8001..."
python3 -m vllm.entrypoints.openai.api_server \
    --model $FORMALIZER_MODEL \
    --port 8001 \
    $FORMALIZER_LIMIT \
    --served-model-name "deepseek-formalizer" &

# Wait for Formalizer to heartbeat
echo "Waiting for Formalizer to stabilize (heartbeat at :8001)..."
until curl -s http://localhost:8001/v1/models > /dev/null; do
    sleep 5
done
echo "Formalizer is ACTIVE."

# 5. Summary
echo "--- [SUCCESS] Spire Proof Backends are synchronized ---"
echo "Proposer (Qwen3-32B)   : http://localhost:8000"
echo "Formalizer (DeepSeek) : http://localhost:8001"
echo ""
echo "CAUTION: Verify Blackwell FP8 performance empirically."

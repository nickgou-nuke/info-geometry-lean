#!/bin/bash
# Autoformalization Background Harness

echo "Scanning InfoGeometry codebase for optimization targets..."
# (In a real run we would find heavy proofs or sorrys)
echo '{"query": "Translate the native_decide brute force steps in lean/DAG/DiracLaplacian.lean to CAS and rewrite the proof in O(1).", "file": "lean/DAG/DiracLaplacian.lean"}' > targets.jsonl
echo '{"query": "Replace simpa using chains in lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean with CAS certificates.", "file": "lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean"}' >> targets.jsonl

echo "Starting OpenGauss batch swarm manager..."
cd OpenGauss
venv/bin/python batch_runner.py \
  --dataset_file=../targets.jsonl \
  --batch_size=8 \
  --run_name=autoformalize_compression_pass \
  --model=anthropic/claude-opus-4.6 \
  --enabled_toolsets=autoformalize,file \
  --save_trajectories=True > ../opengauss_swarm.log 2>&1 &

echo "Background harness launched. PID: $!"

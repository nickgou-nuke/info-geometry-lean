# Autonomous Math Pipeline

This package wires one end-to-end lane:

1. deep research planning/retrieval/verification,
2. evidence packet conversion,
3. Socratic expansion,
4. Pauli admissibility audit,
5. Lean target synthesis,
6. Lean scaffold generation,
7. compiler loop check,
8. memory ingestion.

Entrypoint:

```bash
python3 tools/infra/autonomous_math/research_controller.py \
  --goal "Formalize support-restricted modular Hamiltonian on Preg" \
  --allowed-sources web
```

Outputs:
- run state JSON under `reports/research/`,
- optional final report markdown (if gates pass),
- generated Lean draft under `reports/research/generated_lean/`,
- append-only memory row in `reports/research/autonomous_memory.jsonl`.


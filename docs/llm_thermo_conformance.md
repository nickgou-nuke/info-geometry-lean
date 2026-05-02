# LLM Thermo Conformance Checker

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This document describes runtime conformance checks for the finite thermo lane:

- `InfoGeometry.LLM.KMSSoftmaxBridge`
- `InfoGeometry.LLM.RouterFreeEnergyBridge`
- `InfoGeometry.LLM.PromptDefectRegularization`

Tool:
- `tools/infra/llm_thermo_conformance.py`

Schema:
- `tools/schema/llm_thermo_trace.schema.json`

## Purpose

Given JSONL trace rows extracted from an open-weights run, the checker computes
numerical residuals for theorem-shaped identities, including:

- softmax simplex normalization (`sum(weights)=1`)
- Gibbs/KMS consistency (`weights ≈ softmax(-beta*energies)`)
- log-partition consistency (`massieu ≈ log(partition)`)
- entropy/free-energy identities
- defect quarantine checks (`defect_output_norm ≈ 0`, `defect_weight_sum ≈ 0`)

## Input

Each line is one JSON object. Fields are optional; checks run only when required
fields are present.

Example row:

```json
{
  "trace_id": "run42/layer3/token17",
  "beta": 0.75,
  "weights": [0.70, 0.20, 0.10],
  "energies": [0.0, 1.2, 2.0],
  "partition": 2.130421,
  "massieu": 0.756,
  "internal_energy": 0.44,
  "entropy": 0.801,
  "free_energy": -1.008,
  "defect_output_norm": 0.0,
  "defect_weight_sum": 0.0,
  "active_weight_sum": 1.0
}
```

## Run

```bash
python3 tools/infra/llm_thermo_conformance.py \
  --input traces/runtime_router.jsonl \
  --json-out reports/llm/thermo_conformance.json \
  --md-out reports/llm/thermo_conformance.md \
  --strict-schema \
  --fail-on-violation
```

## Output

- JSON summary with per-check counts, pass/fail, residual percentiles.
- Markdown summary for quick audit.

Exit code:

- `0` when no failing check instance (or `--fail-on-violation` not set).
- `2` when violations exist and `--fail-on-violation` is enabled.

## Notes

- This checker is an empirical witness lane, not a replacement for Lean proofs.
- It is designed to validate runtime traces against already-proved finite
  theorem surfaces.

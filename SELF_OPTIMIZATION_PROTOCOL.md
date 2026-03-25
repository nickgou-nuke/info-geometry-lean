# Self-Optimization Protocol

This repository supports guarded self-analysis. It does not authorize uncontrolled self-editing.

## Allowed loop

1. inspect code directly;
2. classify declarations semantically;
3. make a narrow local change;
4. build the affected targets;
5. rerun the maintained DAG pipeline;
6. compare semantic quotient and projection coloring;
7. repeat only if the new signal is cleaner.

## Required guardrails

- no theorem claim without Lean proof;
- no hotspot-driven deletion of valid math;
- no graph-only refactor without file analysis;
- no large concurrent builds;
- no trusting generated reports until they have been refreshed.

## Current enforcing surfaces

- `lake script run strictCheck`
- `scripts/quality/audit_constructivity.py`
- `tools/infra/generate_semantic_quotient.py`
- `tools/infra/generate_projection_coloring.py`
- [skills/lean-canonicalization-policy/SKILL.md](/home/goutev/LEAN4/info-geometry-lean/skills/lean-canonicalization-policy/SKILL.md)

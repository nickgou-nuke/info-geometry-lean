# Autonomous Math Pipeline

> Status: package-local runbook for autonomous-math lane.
> Canonical infra docs: [`tools/infra/README.md`](../README.md), [`docs/LOCAL_TOOLCHAIN_ARCHITECTURE.md`](../../../docs/LOCAL_TOOLCHAIN_ARCHITECTURE.md).
> Markdown governance: [`docs/MarkdownCorpusGovernance.md`](../../../docs/MarkdownCorpusGovernance.md).

This package wires one end-to-end lane:

1. deep research clarify + rewrite front-end,
2. deep research planning/retrieval/verification,
3. evidence packet conversion,
4. Socratic expansion,
5. Pauli admissibility audit,
6. Lean target synthesis,
7. Lean scaffold generation,
8. compiler loop check,
9. memory ingestion.

Entrypoint:

```bash
python3 tools/infra/autonomous_math/research_controller.py \
  --goal "Formalize support-restricted modular Hamiltonian on Preg" \
  --allowed-sources web
```

Optional:

```bash
--clarifier-model gpt-5
--rewriter-model gpt-5
--skip-clarify
--skip-rewrite
```

Outputs:
- run state JSON under `reports/research/`,
- optional final report markdown (if gates pass),
- generated Lean draft under `reports/research/generated_lean/`,
- append-only memory row in `reports/research/autonomous_memory.jsonl`.

## Current Codebase Status

Status pointer refreshed: 2026-04-16 (Europe/Sofia). See [../../../docs/CODEBASE_STATUS.md](../../../docs/CODEBASE_STATUS.md) for the current build/audit state.

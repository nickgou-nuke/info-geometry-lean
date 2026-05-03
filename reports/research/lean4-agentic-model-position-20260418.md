# Lean4 Agentic Model Position (2026-04-18)

> Status: `generated/historical report`
> Audited: 2026-05-02
> Note: Treat this as a snapshot. Regenerate before relying on it.
> See: [README.md](../../README.md), [docs/README.md](../../docs/README.md), [docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md)

For this Lean4 agentic toolchain, the strongest practical architecture is a dual-model prover lane: a high-diversity generator plus a strict formalizer, both gated by Lean compilation. In current terms (April 2026), `DeepSeek-Prover-V2-7B` is the best local formalization core, `Goedel-Prover-SFT` is the strongest small open alternative, and `Leanstral-2603` is most useful as the long-context planner/orchestrator when memory allows. At the top end, `DeepSeek-Prover-V2-671B` remains the best absolute prover class, but it is infrastructure-heavy. The most stable outcome for this repository is therefore a retrieval-backed, graph-aware pipeline in which hypothesis generation and proof emission are separated, and final truth is always decided by `lake env lean` and the existing strict gates.

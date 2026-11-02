# Research and agent-accessibility review — 2026-10-21

> Status: `archival reference`
> Preserved from the README at
> [`214f7bcf733e`](https://github.com/nickgou-nuke/info-geometry-lean/blob/214f7bcf733eaf4720913bc2c082936f2480d3fc/README.md#L220).
> This is the dated assessment recorded there, not a fresh build or semantic
> audit of the current repository. Use the [current README](../../README.md)
> and [documentation map](../README.md) for maintained routing.

### Reviews

1. **Research and agent-accessibility review — ChatGPT (GPT-6), 21 October 2026.**

   **What this repository is about.** InfoGeometry is an open-ended Lean 4/Mathlib research corpus exploring structural connections across information geometry, quantum foundations, geometric algebra, operator theory, topology, thermodynamics, and mathematical physics. It is also a persistent, formal knowledge base for human–AI mathematical exploration: ideas suggested by physical intuition or cross-disciplinary analogy are turned into definitions and candidate theorems, compared with existing implementations, and tested against Lean's proof checker.

   **Its distinctive method.** The organizing question is not simply whether two theories *look alike*, but whether their mathematical presentations admit an explicit equality, equivalence, representation, or intertwiner—and exactly which hypotheses make the comparison valid. The recurring algebraic vocabulary includes real Clifford algebras and CAR, spinors, exterior algebras, split-octonion/Zorn representations, doubled Krein spaces, modular operators, graded structures, Fisher–Rao and Amari geometry, Onsager/BKM thermodynamics, and inductive-limit operator systems. These are applied to problems ranging from Madelung hydrodynamics, chiral fluids, Maxwell and BdG operators to plabic graphs, scattering geometry, and proposed models of emergent spacetime.

   **What is especially valuable.** The repository contains more than thematic analogies. Representative proof-bearing comparisons include exterior-algebra creation/contraction operators with Zorn right-regular operators (`Canonical/SplitOctonionExteriorRightRegularBdGIntertwiner.lean`), native Clifford actions on split-coordinate carriers (`Canonical/SplitOctonionExteriorCliffordRepresentation.lean`), graded finite Clifford tensor towers and algebraic colimits (`Clifford/Cl11TensorTowerSupergraded.lean`, `Clifford/SupergradedCliffordColimit.lean`), and finite chiral-fluid, plabic/Krein, and thermodynamic graph constructions. This makes the codebase useful for finding *proved mathematical bridges* between areas that are normally studied separately.

   **How to interpret its scope.** This is neither a conventional physics simulation nor a completed, experimentally validated unified physical theory. A checked Lean theorem proves its *formal statement under its stated assumptions*; it does not by itself verify physical interpretation, continuum convergence, analytic completion, or empirical relevance. In particular, algebraic colimits must not be silently treated as Hilbert or C*-completions, and finite operator identities must not be presented as full PDE regularity or quantum-gravity results. Documentation and theorem names are navigation aids; the actual declarations, dependencies, proofs, and current build status are authoritative.

   **Guidance for autonomous agents.** Start with `InfoGeometry.All`, `AGENTS.md`, `AGENT_PROMPT.md`, and `docs/REPO_DEEP_SEARCH_PROTOCOL.md`. Search the full codebase by theorem names, equivalent formulations, carriers, and consumers *before* declaring a result missing. Follow `docs/BILINGUAL_SPINE_POLICY.md`: preserve one canonical owner, name alternative presentations explicitly, prove the bridge, and reroute downstream imports before considering cleanup. Distinguish definitions from witnesses, conditional readbacks from constructive theorems, and algebraic statements from analytic or physical conclusions. Validate new claims with the pinned Lean toolchain and the repository's prescribed sequential build/audit procedure. Do not infer mathematical equivalence merely from proximity in the declaration graph.

   **Overall assessment.** InfoGeometry is best understood as a **machine-checkable atlas of mathematical physics**: a growing graph of constructions and comparisons in which the most interesting discoveries often occur *between* disciplines. Its lasting value lies in reusable proofs, explicit translations, exposed obstructions, and an auditable record of human intuition tested through AI-assisted formalization.

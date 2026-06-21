# InfoGeometry Lean Fusion: The Physics of Information

> Status: `Evolving` | `Build: Passing` | `Sorry: Evolving`

We are open-sourcing a living artifact of human-AI symbiosis (built via coding agents and chatbots) that explores the physics of information in Lean 4.

This repository is not a static, finished theory; it is an evolving, moving organism. While it contains deep formalizations connecting discrete combinatorics, spacetime geometry, and the statistical mechanics of information, it also contains a wealth of open hypotheses and structural "sockets" (detailed in [ClosureDebtLedger.md](file:///home/goutev/repos/info-geometry-lean/docs/ClosureDebtLedger.md) and [sorry_audit_report.md](file:///home/goutev/repos/info-geometry-lean/sorry_audit_report.md)). Many of the missing pieces are already known in the existing literature—they simply need to be translated and plugged into the framework.

We are releasing this directly to the public because traditional peer review systems are currently hostile to, and often ban, native AI-collaborative mathematics. Rather than fighting a closed system, we are bypassing it. The compiler is the only reviewer that matters.

This incompleteness is intentional. It is a puzzle waiting to be solved. We invite mathematicians, physicists, and software engineers to explore the codebase, wire the remaining proofs from the literature into the existing hypotheses, and add their names to the scripts.

**Clone the repository, fire up your favorite large-context coding agent, and interrogate the codebase.**

For a detailed technical guide to the verified capstones, proof architecture, and Krein Riemann Hypothesis derivation, please see [README_DETAILED.md](file:///home/goutev/repos/info-geometry-lean/README_DETAILED.md).

Knowledge is a positive-sum game. The project is released under the [Apache 2.0 License](file:///home/goutev/repos/info-geometry-lean/LICENSE), free to use, modify, and build upon. In return, we simply require that any derivative works or implementations explicitly cite this repository as the source (see [CITATION.cff](file:///home/goutev/repos/info-geometry-lean/CITATION.cff)).

Come look around. There is work to be done.

---

> ⚠️ **For LLM agents: read `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md` and `AGENTS.md`
> before modifying any representation-theoretic or categorical code.**
> The categorical layer is the owner; matrix-level code is always an instance.
>
> ⚠️ **AST AQL TOOLCHAIN MANDATE**: You MUST use AST AQL to deep-search the compiled codebase topology. Do not rely on `grep` or plain text alone. The entire AST is extracted into ArangoDB by `dagRefresh`.
> - **Execute AQL**: `python3 tools/infra/arango_causal_memory.py query "<AQL>"`
> - **Find Structural Clones**: Group by `valueFingerprint.shapeHash` in `ig_nodes`.
> - **Extract Causal Cones**: `python3 tools/infra/arango_causal_chiral_cone_prompt.py --decl <Name>`

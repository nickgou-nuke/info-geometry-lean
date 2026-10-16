# OpenGauss / TeamAntigravity: Assume-and-Recurse Top-Down Protocol

> Status: Operational Law for Multi-Agent Theorem Proving in `info-geometry-lean`.  
> Baseline Standard: `QMS-SOP-IAA-001`, `QMS-POL-OGP-002` (`docs/policy/OPENGAUSS_PROTOCOL_EXTENSIONS.md`), and local extension of [`math-inc/opengauss`](https://github.com/math-inc/opengauss).

---

### I. The Three-Tier TeamAntigravity Architecture

Whereas upstream `math-inc/opengauss` (`OpenGauss/swarm_manager.py`) spawns flat background PTY sessions running the 9 `lean4-skills` commands directly in the repository root, the **TeamAntigravity Protocol** organizes native subagents (`invoke_subagent` / `define_subagent` / `send_message` in Antigravity; `collaboration.spawn_agent` in Codex) into three strictly separated tiers:

1. **The Leader (Strategic Gatekeeper)**:
   - Holds the global mathematical direction, the high-level causal poset ($\mathcal{P}_0 \longrightarrow \mathcal{P}_4$), and the ledger of dead routes.
   - Operates in a lean, protected context window. Does not read verbose compiler dumps or hundreds of tool calls.
   - Strictly gatekeeps every route report from the orchestrator.

2. **The Orchestrator (Tactical Engine)**:
   - Coordinates worker waves, manages tactical state (`PLAN.md`), and executes ground-truth verification against disk and the compiler via `tools/infra/opengauss_cli.py`, `tools/infra/opengauss_screener.py`, and `tools/infra/run_locked_lake_build.py`.
   - Never accepts agent text summaries as proof; runs locked Lake builds and `#print axioms` audits directly.
   - Enforces the **Subagent Sandbox Mandate**: all delegated workers write exclusively to new sandbox files (`scratch/`), never touching live owner files. Only the Orchestrator promotes kernel-verified code into `lean/InfoGeometry/`.

3. **The Worker Swarm (Single-Task Sandboxed Subagents)**:
   - **Scout / Researcher (`research` subagent, `/discover`)**: Read-only search across `lean/InfoGeometry/`, Mathlib, and `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md` before any new carrier or theorem is posited (Gate 0).
   - **Prover (`self` subagent, `/prove`, `/draft`)**: Derives tactic scripts for a single leaf lemma inside an isolated sandbox file (`scratch/<task>_leaf.lean`), supplied with full mathematical context by the Orchestrator.
   - **Refuter (`self` or `research` subagent, `/check`, `/refute`)**: Concurrently attacks every posited child signature against the **17-Trap Catalog** (`TRAP_CATALOG.md`, `T1–T17`) and attempts concrete counterexamples.
   - **Independent Gate 2 Auditor (`A-A`, `/review --gate GATE_2`)**: Separate non-overlapping subagent auditing trap compliance, non-commutativity witnesses (T16), and model non-degeneracy witnesses (T17 / Gate 2.5).
   - **Independent Gate 4 QA (`QA-A`, `/review --gate GATE_4`, `/certify`)**: Separate non-overlapping subagent auditing 0 `sorry`, 0 `admit`, and companion `*Audit.lean` `#print axioms` purity.

---

### II. The Assume-and-Recurse Protocol

1. **Gate 0 — Pre-Flight Discovery (`/discover`)**:
   - Run `python3 tools/infra/opengauss_cli.py discover --query "<concept>"` and check `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md` to reuse canonical owners rather than inventing duplicate wrappers. `/discover` returns candidates; it is not authoritative proof that a declaration exists, is absent, or means what its name suggests.
   - Load active `TypedObstructionPacket` files from `artifacts/residue_quarantine/` so previously refuted routes are banned upfront.
   - Before any theorem signature or code proposal, read the cited owner declarations and record a **Ground-Truth Theorem Contract**: exact carrier/operations, exact existing theorem statements and proof/assumption status, relevant imports and consumers, the narrow missing statement, and nearby claims left unproved. Use `docs/REPO_DEEP_SEARCH_PROTOCOL.md` for the search scope. Cite file plus declaration (and line when available); search results, docstrings, user-supplied code, prior agent summaries, and output from another tool are leads only.
   - The coordinator must reject a proposed claim whose Lean type, assumptions, or carrier do not match the contract. If two owners use different carriers or conventions, establish an explicit proved transport before composing them. A successful build certifies the term at its stated type, not the informal interpretation attached to it.
   - Organize the translation as two paths meeting at a DAG-emergent archetype: **concept input → candidate symbolic archetype**, and **compiler-backed declarations/dependency edges → AST/AQL fingerprints and hash navigation → forward/backward causal cones and multi-apex cone cross-sections → graph/SCC/topology layers → code-derived archetype candidates**; then descend to **raw owner declarations → formal theorem**. SCCs are one graph layer, not the entire discovery mechanism. Follow `docs/ASTAQLHASH-HOWTO.md` and `docs/ARANGO_DAG_REFRESH_METHODOLOGY.md` to check graph-generation/source provenance, preserve seed/apex provenance, inspect shared cross-section nodes, and verify raw-to-overlay descent. Hash matches, SCC membership, graph proximity, and derived scores are navigation evidence only; inspect exact declaration types and proofs before assigning meaning or equivalence. At every translation, record the invariant preserved, information discarded, and granularity. Treat the ladder as a refinement/filtering workflow, not an assumed categorical functor or equivalence. Distinct granularity levels belong in the causal poset only when their dependency is justified by an owned map or theorem.

2. **Gate 1 — Top-Down Positing & Glue Compilation (`/prove`, `/draft`)**:
   - Start from the verified gap in the Ground-Truth Contract; do not copy a generated blueprint into the owner before checking every declaration against the live source.
   - Begin with the headline theorem signature.
   - Posit intermediate decomposition lemmas whose types match **exactly what the parent consumer needs**.
   - Immediately prove the parent using the posited lemmas (`by exact h_lemma ...`) to compile the glue before attempting the leaf proofs.
   - A missing prerequisite is posited as an explicit, narrowly-typed `sorry` child in the sandbox, which becomes the next leaf target.

3. **Consumer-Minimal Weakening (Anti-T11 Law)**:
   - Never posit a child stronger than the parent consumes.
   - If the parent only consumes a trace or sum bound $\sum a_i \le C$, do not demand $a_i \le C / n$ pointwise.
   - If the parent only consumes an existential witness, do not convert it into a universal input (Anti-T7 Law).

4. **Gate 2 & Gate 2.5 — Dedicated Adversary Pairing (`/refute`, `/check`, `/quarantine`)**:
   - For every non-trivial leaf node or posited signature, dispatch a concurrent `Refuter` subagent and run `python3 tools/infra/opengauss_cli.py refute <file> --strict`.
   - The refuter's null hypothesis is that the proposition is false, vacuous, or a scalar surrogate (T16/T17).
   - If the refuter finds a counterexample or flags a T1–T17 trap, stop the prover immediately, isolate the failure via `python3 tools/infra/opengauss_cli.py quarantine`, adjust the signature, and re-glue.
   - The independent auditor must compare the intended mathematical statement with (i) the contract’s source references, (ii) the actual Lean theorem type and hypotheses, and (iii) the consumer. It must reject “compiled, therefore correct” reasoning, stronger prose than the type supports, and assertions copied from summaries without owner-source confirmation.

---

### III. Ground Truth & Anti-Compaction Re-Hydration

1. **Ground Truth Over Reports**:
   - Subagent reports are candidate suggestions, not conclusions.
   - Truth is established exclusively by:
     - `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <TargetModule>` exit code 0.
     - `python3 tools/infra/opengauss_screener.py <file> --strict` exit code 0 (0 traps across T1–T17).
     - Companion `<Module>Audit.lean` (`python3 tools/infra/opengauss_cli.py certify --file <file> --write-audit`) evaluating `#print axioms` strictly to a subset of `[propext, Classical.choice, Quot.sound]`.
     - Git index staging (`git add`) protecting verified work from accidental loss.
   - For continued work, inspect the current worktree, staged diff, imports, and owner source again. Re-verify any prior build or commit claim from current process/build output and Git objects/refs; a handoff is not evidence by itself.

2. **The M10 Anti-Compaction Re-Hydration (`/handoff`, `/autoprove`)**:
   - Auto-compaction is a normal operational event during long-running formalizations.
   - When context compaction occurs, the agent immediately re-hydrates from:
     1. `PLAN.md` (serialized via `opengauss_cli.py handoff`).
     2. `artifacts/residue_quarantine/*.json` (banned search directions and trap obstructions).
     3. `git status` and staged files.
     4. Direct inspection of the latest Lean owner files.
   - Disk and the Lean kernel always supersede in-memory conversation summaries.


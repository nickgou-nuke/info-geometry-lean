---
name: opengauss
description: "Run OpenGauss-style project workflows natively in Codex CLI or Antigravity for this Lean repository: prove, check, refute, draft, review, checkpoint, refactor, golf, autoprove, formalize, autoformalize, handoff, discover, quarantine, or certify using the repository's 17-Trap Catalog, Gate 0-4 pipeline, and locked verification rules."
---

# OpenGauss workflow for Codex CLI & TeamAntigravity

This skill is the project-local entry point for OpenGauss-style workflows.
It uses the current session and repository tools (`tools/infra/opengauss_cli.py`
and `tools/infra/opengauss_screener.py`); it does not install or run the
upstream `OpenGauss/` PTY daemon, create a second persistent queue, or start
unattended background swarms. Collaborating subagents may provide bounded
research, sandboxed proof proposals, and adversarial reviews, but the
coordinating agent owns source promotion and the final verification evidence.

For explicit multi-agent work, follow:
- `docs/CODEX_AGENT_SWARM_PROTOCOL.md` (Codex `collaboration.spawn_agent`)
- `.agents/plugins/opengauss/skills/opengauss_commands/SKILL.md` (15-command CLI reference)
- `.agents/plugins/opengauss/reference/TOP_DOWN_PROTOCOL.md` (3-Tier Leader → Orchestrator → Sandbox Worker Swarm & Assume-and-Recurse loop)
- `.agents/plugins/opengauss/reference/TRAP_CATALOG.md` (17-Trap Catalog `T1–T17`, including `T16` Anti-Surrogate and Gate 2.5 / `T17` Model Witnessing)
- `docs/policy/OPENGAUSS_PROTOCOL_EXTENSIONS.md` (`QMS-POL-OGP-002`, Gate 0 through Gate 4 lifecycle)
- `docs/INDEPENDENT_AGENT_AUDIT_SOP.md` (mandatory non-overlapping G-A, A-A, and QA-A roles)

The coordinating agent owns existing-file edits, coordinates checks, and
records their evidence; it does not replace the distinct A-A or QA-A roles.
This session-level team is distinct from the repository's Hive workers,
vendored Antigravity SDK, and Archon/Python queue; choose one scheduler per
theorem task. Hive worker labels and separate Hive processes do not, by
themselves, establish distinct QMS agent instances. In particular, a model
prompt called an “auditor” inside the authoring process is self-review and
cannot satisfy A-A or QA-A. A-A and QA-A each require a different agent/context;
QA-A must be distinct from both G-A and A-A and rerun the decisive checks.

## Workflow selection (15 Native Commands via `tools/infra/opengauss_cli.py`)

Infer the requested mode from the user request, or ask only if the intended
deliverable is materially ambiguous:

- **discover (`opengauss_cli.py discover --query "..."`)**: Gate 0 pre-flight search across `lean/InfoGeometry/` and Mathlib to reuse canonical carriers and prevent duplicate wrappers. `--local-dag-context` adds read-only offline `artifacts/dag/index` and LeanTrail context. For live graph context, pass one or more exact `--dag-apex Qualified.name` values; bounded prerequisite and consequence cones are queried separately and returned as navigation only. `--backward-depth`, `--forward-depth`, `--cone-limit`, and optional `--dag-generation-id` bound and identify that query. Unknown freshness stays unknown; no graph result never establishes declaration absence.
- **Pantograph memory**: Existing `pantograph_arango_stream.py`, `pantograph_arango_replay.py`, and `pantograph_evidence_packet.py` preserve source snapshots, request/response traces, and environment bindings. Consult a session only when its exact candidate/source binding is known; replay is an explicit separate action. A matched replay may guide tactic navigation, but it is not a Lean owner build, kernel axiom audit, or independent QMS review and cannot promote a theorem.
- **prove / draft (`opengauss_cli.py prove` / `draft`)**: Top-down assume-and-recurse decomposition; posit consumer-minimal child lemmas (Anti-T11 Law), compile the parent glue immediately in a `scratch/` sandbox, and close leaf lemmas.
- **check / refute (`opengauss_cli.py check` / `refute <paths> --strict`)**: Gate 2 & Gate 2.5 adversarial screening against counterexamples, Git pre-commit/pre-push hook rules, and the **17-Trap Catalog (`T1–T17`)**, including `T16` (4-part Anti-Surrogate / Operator-Algebraic Root gate) and `T17` (Gate 2.5 Mandatory Model Witnessing: every `structure`/`class` requires a closed constructive inhabitant or `Inhabited` instance free of `axiom`/`sorry` taint).
- **quarantine (`opengauss_cli.py quarantine`)**: Pillar II residue isolation; package refuted statements or trap violations into immutable `TypedObstructionPacket` JSONs in `artifacts/residue_quarantine/`.
- **autoprove / handoff (`opengauss_cli.py autoprove` / `handoff`)**: Track open `sorry` leaves across waves, ingest banned routes from `artifacts/residue_quarantine/`, and serialize M10 anti-compaction state to `PLAN.md`.
- **refactor / golf (`opengauss_cli.py refactor` / `golf`)**: Identify monolithic proof blocks (>25 lines) for helper extraction and compress redundant tactic sequences (`simp; ring`, `by exact rfl`) while preserving semantics.
- **formalize / autoformalize (`opengauss_cli.py formalize` / `autoformalize`)**: Align mathematical statements or CAS identities with canonical categorical owners into narrowly scoped candidate Lean declarations (`verified: false` until kernel-checked).
- **review / certify (`opengauss_cli.py review <paths> --gate GATE_2|GATE_4 [--verify-kernel]` / `certify --file <file> [--write-audit] [--verify-kernel]`)**: Automated source preflight and optional companion `<Module>Audit.lean` `#print axioms` kernel certification. These commands do not perform an independent semantic audit. `--gate GATE_4` without `--verify-kernel` returns `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`; full kernel verification requires `--verify-kernel` under the shared build lock, and still does not replace independent A-A/QA-A review.
- Review also runs source checks for repository-authored axioms and proof holes, and rejects a theorem that merely constructs a multi-field proposition bundle from other field proofs. The pre-commit rule is name-independent; a predicate structure such as an `Is...` relation remains valid when it defines a mathematical property and is not used as an aggregate theorem receipt. Before committing, `/review` and `/checkpoint` must run `python3 tools/quality/proof_proxy_staged_gate.py` against the staged Lean sources. Foundational axioms reported as dependencies by Lean are distinct from authored `axiom` declarations; authored axioms are prohibited.
- The staged proof-proxy gate fails closed when either checker source differs between the Git index and worktree, because the hook executes checker code from the worktree while screening Lean blobs from the index. Never bypass `proof_proxy_staged_gate.py` by importing `check_text()` directly in inline Python; always run `python3 tools/quality/proof_proxy_staged_gate.py [paths...]` and `python3 tools/quality/proof_proxy_diff_gate.py` so diff-level declaration-deletion, multi-line `/-! ... -/` debt-burial, and checker-index consistency checks execute. Never silence unused hypothesis binders (`T4`) with `_h` prefixes or no-op discards (`let _ := h`, `have _ := h`, `clear h`), and never package conclusions as hypotheses (`T6`) via `rwa`, `simpa`, `assumption`, or redundant symmetry binders.
- **checkpoint (`opengauss_cli.py checkpoint -m "..." --stage-path <file>`)**: Summarize current evidence and stage verified paths (`git add`) under the Continuous Tracking Mandate.

## Causal workflow (Gate 0 – Gate 4)

1. **Scope & Gate 0 Discovery** — identify the requested owner file(s), theorem/module, and compiler diagnostic; run `opengauss_cli.py discover` and inspect `artifacts/residue_quarantine/` so banned routes and duplicate carriers are avoided upfront. Treat `/discover` as candidate navigation only, never as proof of existence, absence, correctness, or novelty.
2. **DAG-Emergent Archetype Ladder + Ground-Truth Contract (required before proposing code)** — reconcile two provenance paths: concept input → candidate symbolic archetype, and compiler-backed Lean declarations/dependency edges → AST/AQL fingerprint/hash navigation → forward/backward causal cones and multi-apex cone cross-sections → graph/SCC/topology overlays → code-derived archetype candidates. SCCs are one layer, not the whole discovery mechanism. Follow `docs/ASTAQLHASH-HOWTO.md` and `docs/ARANGO_DAG_REFRESH_METHODOLOGY.md`: check generation/source freshness where available, preserve each cone seed/apex provenance, inspect shared nodes reached from multiple apices, and descend every graph/hash candidate to its raw Lean declarations before interpreting it. Hashes, SCCs, overlays, scores, and graph proximity are navigation evidence, never proof of equivalence or meaning. Then map candidates to repo-owned Lean objects and formal theorems, recording what each translation preserves/discards and the granularity at each level. Treat this as a traceable refinement/filtering ladder, not an assumed functor or adjunction. Record exact file/declaration references for (a) the mathematical claim separated from rhetoric, (b) carrier and conventions, (c) existing proved results versus assumptions, (d) consumer’s minimal requirement, (e) narrowly stated missing delta, and (f) claims not established. Follow `docs/REPO_DEEP_SEARCH_PROTOCOL.md`; a name search, generated report, user-supplied snippet, agent summary, or successful compile is not a substitute. If the source does not support the requested claim, correct the contract before editing. Different carriers require an explicit map and proved compatibility lemma.
3. **Preflight** — read `AGENTS.md`, `docs/CANONICAL_AGENT_PIPELINE.md`, and `docs/HIVE_AGENT_COMMANDMENTS.md`; inspect the working tree and preserve all pre-existing changes. On resumed/compacted work, re-read live owners and diffs and verify prior build/Git claims from current evidence.
4. **Analyze & Plan (Gate 1)** — state the minimal causal repair or consumer-minimal decomposition from the contract. Separate actual compiler errors from warnings or slow tactics. CAS/SymPy/GAP output may suggest a finite witness, but is never proof evidence by itself.
5. **Sandbox Edit & Gate 2 / 2.5 Screen** — candidate subagents write proposals strictly to new sandbox files (`scratch/`); only the coordinating agent edits live owner files. Run `python3 tools/infra/opengauss_screener.py <file> --strict` (0 traps across `T1–T17`, enforcing `T16` non-commutativity witnesses, Gate 2.5 / `T17` model witnesses, and pre-commit proof-proxy field/debt rules). A separate auditor must check the theorem’s mathematical meaning against the Ground-Truth Contract and owner statements; static screening and kernel compilation cannot perform that semantic comparison. Never replace proof debt with `sorry`, `axiom`, `admit`, `unsafe`, scalar surrogates, renamed claims, or vacuous propositions.
6. **Independent Audit** — the code author is G-A and must not audit its own artifact. Dispatch an A-A that did not author the patch to review the exact diff and relevant owners; the A-A is read-only. Revise only in response to specific findings, then send the corrected diff back for A-A review. Read `docs/INDEPENDENT_AGENT_AUDIT_SOP.md`; an automated CLI review, compiler, or author self-check cannot substitute for A-A.
7. **Verify & Gate 4 Certify** — before compilation, inspect active compiler/build processes. Run builds sequentially through `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <target>`, and run kernel verification via `python3 tools/infra/opengauss_cli.py review <file> --gate GATE_4 --verify-kernel` and `python3 tools/infra/opengauss_cli.py certify --file <file> --write-audit --verify-kernel`. Do not run cache-destructive commands or kill builds without explicit authorization.
8. **Independent Acceptance** — after the final edits and decisive checks, dispatch a QA-A distinct from both G-A and A-A to rerun those checks and confirm scope. The author cannot accept the artifact. If QA-A requests changes, return to the A-A review and verification steps before acceptance.
9. **Report & Checkpoint** — distinguish source changes, commands actually run, observed diagnostics, A-A and QA-A dispositions, and remaining uncertainty. Stage verified changes immediately via `opengauss_cli.py checkpoint` (`git add`). Never report an unverified or static-only check as kernel-accepted, and never let a compiled theorem inherit a stronger interpretation than its Lean type and hypotheses support.

## Existing project queue

When the user explicitly requests execution of a queued theorem task, use the
single canonical queue rather than creating an OpenGauss queue:

```bash
python3 tools/infra/agent_orchestrator_queue.py status
python3 tools/infra/agent_orchestrator_queue.py run-next
```

Follow `docs/CANONICAL_AGENT_PIPELINE.md` and
`docs/HIVE_AGENT_COMMANDMENTS.md` for the Researcher + Algebraist → Formalist →
Critic → Archivist sequence, artifact locations, and runtime constraints. Do
not start the queue implicitly for an ordinary proof/review request.

## Workflow boundaries

- Keep each task narrow and causal; do not launch mass builds to discover an
  unspecified error.
- Do not claim all repository files were audited from a partial target build.
- Do not start background batch runners, cron tasks, or unattended swarm
  processes.
- Do not edit dirty submodules or shared target files that contain pre-existing
  user changes without first reconciling their exact diff.
- Locked Lean kernel compilation and `#print axioms` verification (`--verify-kernel`),
  not static screening alone, CAS agreement, prose, or agent consensus, is the
  acceptance check for Lean source.

---
name: opengauss
description: Run OpenGauss-style project workflows natively in Codex CLI or Antigravity for this Lean repository: prove, check, refute, draft, review, checkpoint, refactor, golf, autoprove, formalize, autoformalize, handoff, discover, quarantine, or certify using the repository's 17-Trap Catalog, Gate 0-4 pipeline, and locked verification rules.
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

The coordinating agent owns existing-file edits and all final Lean/QMS checks.
This session-level team is distinct from the repository's Hive workers,
vendored Antigravity SDK, and Archon/Python queue; choose one scheduler per
theorem task.

## Workflow selection (15 Native Commands via `tools/infra/opengauss_cli.py`)

Infer the requested mode from the user request, or ask only if the intended
deliverable is materially ambiguous:

- **discover (`opengauss_cli.py discover --query "..."`)**: Gate 0 pre-flight search across `lean/InfoGeometry/` and Mathlib to reuse canonical carriers and prevent duplicate wrappers.
- **prove / draft (`opengauss_cli.py prove` / `draft`)**: Top-down assume-and-recurse decomposition; posit consumer-minimal child lemmas (Anti-T11 Law), compile the parent glue immediately in a `scratch/` sandbox, and close leaf lemmas.
- **check / refute (`opengauss_cli.py check` / `refute <paths> --strict`)**: Gate 2 & Gate 2.5 adversarial screening against counterexamples, Git pre-commit/pre-push hook rules, and the **17-Trap Catalog (`T1–T17`)**, including `T16` (4-part Anti-Surrogate / Operator-Algebraic Root gate) and `T17` (Gate 2.5 Mandatory Model Witnessing: every `structure`/`class` requires a closed constructive inhabitant or `Inhabited` instance free of `axiom`/`sorry` taint).
- **quarantine (`opengauss_cli.py quarantine`)**: Pillar II residue isolation; package refuted statements or trap violations into immutable `TypedObstructionPacket` JSONs in `artifacts/residue_quarantine/`.
- **autoprove / handoff (`opengauss_cli.py autoprove` / `handoff`)**: Track open `sorry` leaves across waves, ingest banned routes from `artifacts/residue_quarantine/`, and serialize M10 anti-compaction state to `PLAN.md`.
- **refactor / golf (`opengauss_cli.py refactor` / `golf`)**: Identify monolithic proof blocks (>25 lines) for helper extraction and compress redundant tactic sequences (`simp; ring`, `by exact rfl`) while preserving semantics.
- **formalize / autoformalize (`opengauss_cli.py formalize` / `autoformalize`)**: Align mathematical statements or CAS identities with canonical categorical owners into narrowly scoped candidate Lean declarations (`verified: false` until kernel-checked).
- **review / certify (`opengauss_cli.py review <paths> --gate GATE_2|GATE_4 [--verify-kernel]` / `certify --file <file> [--write-audit] [--verify-kernel]`)**: Independent QMS audit and companion `<Module>Audit.lean` `#print axioms` certification. Note: `--gate GATE_4` without `--verify-kernel` returns `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED`; full Gate 4 acceptance requires `--verify-kernel` under the shared build lock.
- Review also runs source checks for repository-authored axioms and proof holes, and rejects a theorem that merely constructs a multi-field proposition bundle from other field proofs. The pre-commit rule is name-independent; a predicate structure such as an `Is...` relation remains valid when it defines a mathematical property and is not used as an aggregate theorem receipt. Before committing, `/review` and `/checkpoint` must run `python3 tools/quality/proof_proxy_staged_gate.py` against the staged Lean sources. Foundational axioms reported as dependencies by Lean are distinct from authored `axiom` declarations; authored axioms are prohibited.
- **checkpoint (`opengauss_cli.py checkpoint -m "..." --stage-path <file>`)**: Summarize current evidence and stage verified paths (`git add`) under the Continuous Tracking Mandate.

## Causal workflow (Gate 0 – Gate 4)

1. **Scope & Gate 0 Discovery** — identify the requested owner file(s), theorem/module, and compiler diagnostic; run `opengauss_cli.py discover` and inspect `artifacts/residue_quarantine/` so banned routes and duplicate carriers are avoided upfront.
2. **Preflight** — read `AGENTS.md`, `docs/CANONICAL_AGENT_PIPELINE.md`, and `docs/HIVE_AGENT_COMMANDMENTS.md`; inspect the working tree and preserve all pre-existing changes.
3. **Analyze & Plan (Gate 1)** — separate actual compiler errors from warnings or slow tactics. State the minimal causal repair or consumer-minimal decomposition. CAS/SymPy/GAP output may suggest a finite witness, but is never proof evidence by itself.
4. **Sandbox Edit & Gate 2 / 2.5 Screen** — candidate subagents write proposals strictly to new sandbox files (`scratch/`); only the coordinating agent edits live owner files. Run `python3 tools/infra/opengauss_screener.py <file> --strict` (0 traps across `T1–T17`, enforcing `T16` non-commutativity witnesses, Gate 2.5 / `T17` model witnesses, and pre-commit proof-proxy field/debt rules). Never replace proof debt with `sorry`, `axiom`, `admit`, `unsafe`, scalar surrogates, or vacuous propositions.
5. **Verify & Gate 4 Certify** — before compilation, inspect active compiler/build processes. Run builds sequentially through `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <target>`, and run Gate 4 verification via `python3 tools/infra/opengauss_cli.py review <file> --gate GATE_4 --verify-kernel` and `python3 tools/infra/opengauss_cli.py certify --file <file> --write-audit --verify-kernel`. Do not run cache-destructive commands or kill builds without explicit authorization.
6. **Report & Checkpoint** — distinguish source changes, commands actually run, observed diagnostics, and remaining uncertainty. Stage verified changes immediately via `opengauss_cli.py checkpoint` (`git add`). Never report an unverified or static-only check as kernel-accepted.

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

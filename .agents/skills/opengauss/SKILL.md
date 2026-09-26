---
name: opengauss
description: Run OpenGauss-style project workflows natively in Codex CLI for this Lean repository: prove, review, refactor, formalize, checkpoint, or investigate compiler bottlenecks using the repository's authoritative queue and verification rules.
---

# OpenGauss workflow for Codex CLI

This skill is the project-local Codex entry point for OpenGauss-style workflows.
It uses Codex's current session and repository tools; it does not install or run
the OpenGauss submodule, create a second queue, start background swarms, or
delegate authority to an external agent.

## Workflow selection

Infer the requested mode from the user request, or ask only if the intended
deliverable is materially ambiguous:

- **prove / autoprove**: investigate one named theorem or Lean error, derive a
  structural proof plan, then make the smallest owner-file change and verify it.
- **review**: inspect the named change read-only and report concrete findings,
  prioritizing soundness, theorem honesty, imports, and build impact.
- **formalize / autoformalize**: translate a supplied mathematical statement
  into a narrowly scoped Lean declaration; do not invent hypotheses or claim a
  result stronger than the supplied mathematics supports.
- **refactor / golf**: identify a specific cost or duplication, preserve
  semantics, and compare targeted verification evidence. Do not replace proofs
  merely because a tactic is syntactically short or slow-looking.
- **checkpoint**: summarize current evidence, changed paths, unresolved debt,
  and the exact next action. Do not stage unrelated files or commit unless
  explicitly asked.

## Causal workflow

1. **Scope** — identify the requested owner file(s), theorem/module, desired
   outcome, and any existing compiler diagnostic. Do not scan or rewrite the
   whole repository by default.
2. **Preflight** — read `AGENTS.md`, `docs/CANONICAL_AGENT_PIPELINE.md`, and
   `docs/HIVE_AGENT_COMMANDMENTS.md`; inspect the working tree and preserve all
   pre-existing changes. For a Lean owner, inspect its imports and nearby
   definitions before proposing edits.
3. **Analyze** — separate actual compiler errors from warnings, slow tactics,
   and conjectured bottlenecks. Use source and observed timings as evidence;
   tactic names alone do not establish a performance defect.
4. **Plan** — state the minimal causal repair. CAS/SymPy/GAP output may suggest
   a finite witness or identity, but it is not proof evidence by itself. Any
   certificate must be represented and checked in Lean, and the final theorem
   must still compile in Lean's kernel.
5. **Edit** — only the coordinating Codex agent changes existing owner files.
   Candidate agents, if present, provide read-only analysis or write proposals
   to a new sandbox artifact; they never overwrite owner files. Never replace
   proof debt with `sorry`, `axiom`, `admit`, `unsafe`, vacuous propositions, or
   unverified generated code.
6. **Verify** — before compilation, inspect active compiler/build processes.
   Run builds sequentially through
   `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <target>`.
   For a standalone Lean check, follow the repo's shared-lock and sequential
   build rules. Do not run cache-destructive commands or kill builds without
   explicit authorization.
7. **Report** — distinguish source changes, commands actually run, observed
   diagnostics, and remaining uncertainty. Never report a background job or
   unobserved result as completed.

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
- Lean compilation, not CAS agreement, prose, or agent consensus, is the
  acceptance check for Lean source.

# Repository agent policy

This file governs repository work. Use the current checkout and its source as
the implementation context. The [canonical pipeline](docs/CANONICAL_AGENT_PIPELINE.md)
documents commands and optional integrations; the [runbook](RUNBOOK.md) explains
validation coverage. Archived transcripts and research proposals are context,
not operational instructions or evidence of completed proofs.

## Start from the current checkout

Run commands from the checkout root, discovered with
`git rev-parse --show-toplevel`. Inspect the current commit, remote, and
`git status --short` before editing. A maintainer workstation path is not a
requirement for other checkouts.

Read this file and [docs/CANONICAL_AGENT_PIPELINE.md](docs/CANONICAL_AGENT_PIPELINE.md).
For repository-content questions, follow
[docs/REPO_DEEP_SEARCH_PROTOCOL.md](docs/REPO_DEEP_SEARCH_PROTOCOL.md).
Search related definitions, alternate formulations, imports, instances, theorem
statements, and consumers before claiming that a construction is absent or
incorrect. Report a bounded search as a bounded search.

## Mathematical acceptance

Lean checks a proposition at its declared type. It does not establish that a
physical interpretation, filename, or docstring describes that proposition
faithfully. Read the owner source and record:

1. The precise claim and the actual carrier, operations, and conventions.
2. Reused declarations and their hypotheses, including structure fields that
   supply assumptions rather than construct the desired result.
3. Relevant imports, consumers, and the smallest missing implication.
4. The exact statement proved, validation performed, and remaining debt.

For generated prose or proposed mathematics, use
[epistemic compilation](skills/epistemic-compilation/SKILL.md) and the
[theorem-contract workflow](docs/ALCHEMICAL_QMS_SOP.md). Preserve provenance,
separate proved/conditional/open claims, and order dependencies only when the
corresponding maps or implications have been established. Write incomplete
targets in the task contract; do not insert proof holes into promoted owners.

Do not introduce `sorry`, `admit`, custom axioms, `native_decide`, unsafe proof
bypasses, or vacuous wrappers to obtain acceptance. Audit declaration axiom
dependencies; permitted foundational axioms are `propext`, `Classical.choice`,
and `Quot.sound`. A clean text scan, a successful compilation, and a semantic
review are different checks. Report each at its actual scope. These are
acceptance requirements, not a claim that every tracked historical file passes.

Preserve noncommutative operator content when it is part of the target claim.
Do not replace it with scalar, diagonal, or commuting surrogates. A concrete
finite matrix result must be described with its actual dimension and
hypotheses. Moving to another carrier, a quotient, a categorical colimit,
a completion, or an analytic limit requires the corresponding construction and
compatibility proof.

Reuse existing owners before introducing another bridge. Consult the
[categorical infrastructure map](docs/CATEGORICAL_INFRASTRUCTURE_MAP.md), then
inspect the declarations it points to. Distinguish finite-stage compatibility,
conditional cone transport, a colimit universal property, and analytic
consequences. Native Mathlib analysis remains appropriate when required by the
theorem. Keep owner files focused and expose reusable intermediate lemmas.

## Build, dependency, and cache discipline

[lean-toolchain](lean-toolchain) and [lake-manifest.json](lake-manifest.json)
determine the environment. At source review revision
`214f7bcf733eaf4720913bc2c082936f2480d3fc`, Lean is `v4.34.1` and Mathlib is
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Dependency or toolchain changes require
explicit user authorization. Do not run `lake update` as a routine repair or
change pinned dependencies incidentally.

Inspect running compiler processes before validation. Serialize build, test,
and compilation commands. Use the maintained wrappers:

```bash
python3 tools/infra/run_locked_lean.py lean/InfoGeometry/Path/To/File.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Path.To.Module
```

Replace the example path/module with the actual owner. Both wrappers use
[the shared build lock](tools/build_lock.py). A no-target invocation of
`run_locked_lake_build.py` selects changed owners; an explicit
`--all-default-targets` request selects Lake's default targets. Neither a narrow
check nor a default-target build establishes coverage of every tracked file.
See [RUNBOOK.md](RUNBOOK.md) before making a build-status claim.

Never run `lake clean` or delete `.lake`, `.lake/build`, or `.lake/packages` as a
repair. Do not make dependency directories read-only: normal builds must write
generated artifacts. Follow the source-backed
[cache policy](WARNING_DO_NOT_RUN_CACHE.md) for missing artifacts.
The [build validator](tools/infra/build.py),
[file-check wrapper](tools/infra/run_locked_lean.py), and
[pre-push hook](.githooks/pre-push) reject linked Git worktrees and symlinked
`.lake` or `.lake/packages` roots. Use an independent checkout for builds.
Do not kill a running Lake process without explicit user authorization.

## Changes, checkpoints, and collaboration

Preserve unrelated work. Make the smallest owner-aligned change and review its
diff. Checkpoint task-owned edits promptly with `git add -- <paths>` after
reviewing status; do not stage every workspace change indiscriminately.
Staging is not a backup or permission to restore, reset, delete, or overwrite
someone else's work. Keep generated run debris out of source commits unless
the task explicitly calls for it. Do not edit dirty external submodules unless
requested.

Delegate source-repair proposals to new files in an isolated candidate area.
Give workers the exact owner context and theorem contract. The parent reviews
and integrates candidates into existing owners. Independent read-only analysis
may proceed in parallel; builds and tests remain serialized. Follow the
[native agent-team protocol](docs/CODEX_AGENT_SWARM_PROTOCOL.md) or
[Pi team operations](docs/PI_AGENT_TEAMS_OPERATIONS.md) for the selected runtime.
Confirm actual worker state before reporting that work has started.

Install tracked hooks for a development checkout with
`scripts/install_git_hooks.sh`. The
[staged proof gate](tools/quality/proof_proxy_staged_gate.py) and
[push gate](.githooks/pre-push) check different surfaces; do not bypass them or
describe their presence as evidence that they ran. The
[Hive policy checklist](docs/HIVE_AGENT_COMMANDMENTS.md) records the required
Lean header and the reporting checklist.

## Optional services and domain routing

Arango, graph indexes, Loogle, SymPy, browser oracles, Pi, Hive, Archon, and GEPA
provide navigation, candidates, or execution support. They do not replace Lean
proofs. Their availability, contents, and freshness must be observed for the
current environment; do not assume a running service or complete transcript
ingestion. Resolve endpoints and credentials through maintained configuration,
and keep the declaration DAG, Hive queue, and aiClaw memory lanes distinct.

Oracle outputs belong in candidate/report artifacts. A coding agent inspects
and applies source changes, then runs the relevant checks. Do not stack browser
prompts or bypass the shared ChatGPT lane. Consult the
[canonical transport instructions](docs/CANONICAL_AGENT_PIPELINE.md#browser-oracle-adapters)
before using an optional oracle; older runbooks may describe a different
adapter. Do not claim recovery of hidden reasoning.

| Task | Read before changing owners |
|---|---|
| DAG, namespace, or forwarding-module cleanup | [DAG wire-refactor workflow](skills/lean-dag-wire-refactor/SKILL.md) |
| Categorical, tensor-tower, or colimit work | [Categorical infrastructure map](docs/CATEGORICAL_INFRASTRUCTURE_MAP.md) and [skill catalog](skills/lean-skill-library/) |
| Peirce defects and two-sheet Yang–Mills claims | [Source-grounded framework progress](docs/TWO_SHEETED_YANG_MILLS_FRAMEWORK_PROGRESS.md) |
| Souriau, Bost–Connes, or crystallization claims | [Transition status](docs/SOURIAU_BOST_CONNES_TRANSITION_STATUS.md) |
| Oracle-assisted proof repair | [Repair workflow](skills/socratic-oracle-proof-repair/SKILL.md), checked against the current adapter source |
| Debate/convergence interpretations | [Formal precedent map](docs/DEBATE_ORACLE_CONVERGENCE_MAP.md) |
| AI Studio transcript export | [Transcript export procedure](docs/AI_STUDIO_TRANSCRIPT_EXPORT.md) |

For exterior-algebra constructions, make coefficient types explicit where
needed, such as `Finsupp.single (i, j) (1 : R)`, and use `noncomputable` when
required by the chosen construction. Keep Arnold relations, BCFW recursion,
Klein-quadric decomposability, operator nilpotency, and Bost–Connes partition
functions distinct unless an explicit map and theorem relate them.

End a task with the changed files, exact validation commands and results,
proved or observed scope, and unresolved issues. Do not turn an old report or
a successful local check into a current whole-repository certificate.

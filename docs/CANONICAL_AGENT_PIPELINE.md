# Canonical agent pipeline

Source reviewed on 2026-11-03 against
`214f7bcf733eaf4720913bc2c082936f2480d3fc`. This is an operational map of the
tracked implementation, not a claim that optional services are running or that
the complete repository has passed a fresh build.

The [root agent policy](../AGENTS.md) governs acceptance and changes.
[RUNBOOK.md](../RUNBOOK.md) defines validation coverage. Use this page for
command routing; treat archived transcripts as historical context.

## Checkout and source authority

Start in the current checkout root:

```bash
git rev-parse --show-toplevel
git rev-parse HEAD
git status --short
```

Use that root as the working directory for commands below. Check the remote
before repository edits. `/home/goutev/repos/info-geometry-lean` is a maintainer
environment example, not a required location for clones or hosted sessions.
The implementation already derives roots through
[tools/pathing.py](../tools/pathing.py) and related configuration helpers.

Read [AGENTS.md](../AGENTS.md), the
[Hive checklist](HIVE_AGENT_COMMANDMENTS.md), and the
[repository search protocol](REPO_DEEP_SEARCH_PROTOCOL.md). Lean owner source,
its imported definitions, hypotheses, and compiler results determine what is
formalized. Documentation, graph results, CAS witnesses, and model responses
are evidence or candidates whose claims must be checked against those owners.

## Context and theorem contract

The [context preflight](../tools/infra/context_preflight.py) builds a bounded
navigation packet:

```bash
python3 tools/infra/context_preflight.py "question or target theorem" --include-external
```

Its root list includes `tools`, `scripts`, `src`, `cli`, `extensions`, `lakefile.toml`, `package.json`, and `pyproject.toml`. Keep repo-owned, external-reference, generated-artifact, and runtime evidence separate, and inspect owner declarations before answering.

Before editing a mathematical owner, record the exact claim, carrier,
operations, reused declarations, hypotheses, imports, consumers, smallest
unproved implication, and adjacent claims not established. Follow
[epistemic compilation](../skills/epistemic-compilation/SKILL.md) and the
[theorem-contract workflow](ALCHEMICAL_QMS_SOP.md). A proof of a conditional
statement does not discharge its assumptions. A finite algebraic identity does
not supply a topology, colimit universal property, completion, physical law,
or classification theorem without the corresponding construction and proof.

For declaration-DAG and archetype work, use
[AST/AQL/hash navigation](ASTAQLHASH-HOWTO.md) and
[graph refresh methodology](ARANGO_DAG_REFRESH_METHODOLOGY.md). Preserve source
and seed provenance. Fingerprints, SCC membership, and causal-cone intersections
identify candidates; inspect the actual types and maps to determine their
meaning. Do not refresh a graph just to begin a search or claim freshness
without evidence.

## Lean verification

Inspect active compiler processes and serialize builds and tests. Use the
[file wrapper](../tools/infra/run_locked_lean.py) for one source file and the
[Lake wrapper](../tools/infra/run_locked_lake_build.py) for a module:

```bash
python3 tools/infra/run_locked_lean.py src/InfoGeometry/Path/To/File.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Path.To.Module
```

Replace the example path/module with the actual owner. Both use the shared
lock in [tools/build_lock.py](../tools/build_lock.py). The file check consumes
available imported artifacts; a targeted Lake build manages dependencies.
Keep validation narrow while editing, then run the checks required for the
change's integration and acceptance.

| Requested coverage | Lake wrapper selection |
|---|---|
| Specific owner and dependencies | Explicit module target |
| Changed `InfoGeometry` owners | `--changed`, also the no-target default |
| Registered `proofs` library | Explicit `proofs` target |
| Every Lake default target | Explicit `--all-default-targets` |

`--wfail` requests warnings-as-errors. Extra Lake arguments belong after `--`
and require explicit target/default-target mode; changed-owner mode rejects
them. A successful build certifies only the selected build surface. Separately
review proof holes, axiom dependencies, vacuity, and the relationship between
the Lean statement and the reported claim.

Preserve [dependency pins](../lake-manifest.json) and
[the toolchain](../lean-toolchain). Never clean/delete Lake caches as a repair;
follow [the cache policy](../WARNING_DO_NOT_RUN_CACHE.md). Builds reject linked
worktrees and symlinked Lake roots. Do not kill a running Lake process without
explicit user authorization.

## Browser oracle adapters

Oracle results are candidate/report artifacts. A coding agent reviews and
applies a patch; Lean and semantic review determine acceptance. Use an oracle
only when the task and environment authorize that external interaction.

The current [socratic_clawbot.py](../tools/infra/socratic_clawbot.py) sends
through [chatgpt_browser_harness_driver.py](../tools/infra/chatgpt_browser_harness_driver.py),
which uses [chatgpt_lane_guard.py](../tools/infra/chatgpt_lane_guard.py).
It does not currently delegate its transport to `aiclaw_chat.py`; its legacy
aiClaw platform/base-url/queue options are ignored or deprecated. Its dry-run
prints send metadata and does not contact ChatGPT or validate a proof:

```bash
python3 tools/infra/socratic_clawbot.py \
  --file src/InfoGeometry/Path/To/File.lean \
  --theorem theorem_name --dry-run --json
```

For an authorized repair request with configured browser access, explicit
artifact outputs are available:

```bash
python3 tools/infra/socratic_clawbot.py \
  --file src/InfoGeometry/Path/To/File.lean \
  --theorem theorem_name \
  --candidate-out tmp/oracle_candidates/theorem_name.lean \
  --response-out artifacts/oracle/theorem_name.md \
  --json-out artifacts/oracle/theorem_name.json
```

Keep the complete owner context and relevant errors in the request. Do not
let a generated replacement overwrite an owner automatically, stack prompts
after a possible send, use the old direct port-1956 bridge, inject a prompt
outside the guard, or use Enter as a substitute for a disabled send button.
Recover uncertain final readback before submitting another request.

[aiclaw_chat.py](../tools/infra/aiclaw_chat.py) remains a separate adapter with
explicit queue controls:

```bash
python3 tools/infra/aiclaw_chat.py status
python3 tools/infra/aiclaw_chat.py queue-status --platform chatgpt
```

Follow its returned `queue_state` and `agent_action`: `active` requires waiting;
`needs_readback` requires recovery of the visible final response and recorded
readback before release; `ready` permits one send. Use its prune/release
operations only for the corresponding observed state. See the
[aiClaw runbook](AICLAW_CHATGPT_REVIEW_RUNBOOK.md), checking its commands against
the selected adapter. Google AI Mode has a separate
[browser-harness entrypoint](../scripts/google-ai-search.sh); do not conflate
its state with aiClaw Gemini or ChatGPT.

## Optional Arango and graph services

For the observed Auto-Ontology runtime topology, service startup, host-vs-
Compose distinction, and REST/MCP health checks, see the
[Auto-Ontology agent operations guide](AUTO_ONTOLOGY_AGENT_OPERATIONS.md).

Resolve configuration from [igf.config](../src/igf/config/env_aliases.py),
the [Hive queue](../tools/infra/hive_arango_queue.py), and
the [aiClaw memory adapter](../tools/infra/aiclaw_auto_arango.py).

| Lane | Source default | Configuration |
|---|---|---|
| Declaration/InfoTree DAG | `infogeometry`, port 8530 | `ARANGO_*` |
| Auto Ontology (Terms & Relationships) | FastAPI REST port 3001 / MCP port 3003 (`/mcp`) / Postgres port 5433 (`auto_ontology`) | `.mcp.json` (`nvidia-auto-ontology`), `tools/infra/arango_to_ontology.py` (`--pin-generation`, `--dry-run`), `tools/infra/arango_to_ontology_relationships.py`, `tools/infra/decl_projection.py`, `tools/infra/sql/001_decl_projection.sql`, [ASTAQLHASH-HOWTO.md](ASTAQLHASH-HOWTO.md#auto-ontology-layer-localhost3001-rest-api--localhost3003mcp) |
| Hive task queue | `hive_live`, port 8540 | `HIVE_ARANGO_*` and the documented aliases |
| aiClaw proof/text memory | `aiclaw_auto_rag`, port 8540 | `AICLAW_ARANGO_*` |
| Alexandria literature | `alexandria`, port 8532 in shared configuration | `ALEXANDRIA_ARANGO_*` |

### Unified pipeline runner (`scripts/run_pipeline.sh`)

To run the four-stage ontology/taxonomy/phylogenesis pipeline (narrow-owner locked Lean build, evolution taxonomy contract tests, `repo-phylogeny/v2` export + dashboard generation, and offline/Arango Auto-Ontology bridge dry-run) with a SHA-256 run receipt:

```bash
./scripts/run_pipeline.sh [--skip-lean-build] [--generation-id <ID>] [--report-dir <DIR>]
```

See [docs/PIPELINE_IMPROVEMENT_AND_REFACTORING_PLAN.md](PIPELINE_IMPROVEMENT_AND_REFACTORING_PLAN.md) and [tools/repository_evolution/README.md](../tools/repository_evolution/README.md) for the full 5-level evidence boundary (`Level 1` Lean kernel truth vs. `Level 5` heuristic Python telemetry).

These are defaults, not observed running services. Explicit environment values
can override them. Do not print credentials, assume graph freshness, or claim
complete transcript ingestion without an ingestion record. The
[search protocol](REPO_DEEP_SEARCH_PROTOCOL.md#arangodb-schema-families)
describes collection families; graph evidence remains navigation evidence.
For cross-lane mapping, typed bridge relations, freshness sentinels, and
duplicate-candidate review, follow the
[repository ontology unification playbook](ONTOLOGY_UNIFICATION_PLAYBOOK.md)
and its [agent skill](../.agents/skills/repo-ontology-unification/SKILL.md).

## Pi integration status

**The old root Pi launcher instructions are not runnable from the tracked
source at the reviewed revision.** Root `run.sh`, `lean-prover-tool.ts`, and
`agent-orchestrator.ts` are absent. Although copies exist under `proofs/`,
[extensions/lean-prover-tool.ts](../extensions/lean-prover-tool.ts) and
[extensions/agent-orchestrator.ts](../extensions/agent-orchestrator.ts) forward
to absent root implementations. Adding `extensions/` to the old invocation
does not repair those imports.

[extensions/chatgpt-oracle.ts](../extensions/chatgpt-oracle.ts) contains an
implementation and resolves `tools/infra/aiclaw_chat.py` from the working
directory. The older [proofs/run.sh](../proofs/run.sh) changes into `proofs/`
and contains older environment assumptions. Do not present it as a verified
replacement launcher. Repair the owners and verify the resulting invocation
before restoring an end-to-end Pi quickstart. The Python verification wrappers
above remain separately inspectable entrypoints.

## Python theorem queue and optional Archon wrapper

The [Python queue](../tools/infra/agent_orchestrator_queue.py) reads
`task_queue.json`, uses `proofs/<task-id>.lean` and `proofs/<task-id>.sp`, and
writes reports under `artifacts/agent_orchestrator/`. Run from the repository
root. Its `status` command inspects the queue; `run-next` executes a queued
task and writes state/artifacts:

```bash
python3 tools/infra/agent_orchestrator_queue.py status
python3 tools/infra/agent_orchestrator_queue.py run-next
```

Its implemented order is Researcher and Algebraist, then Formalist, Critic,
and Archivist. Inspect stage outcomes, skipped checks, source hashes, and the
actual Lean result before reporting completion. SymPy results support the
investigation; they do not prove the Lean proposition. The
[AutoMath adapter](AUTOMATH_COLLECTIVE_PIPELINE.md) is another candidate path,
not a new proof authority or implicit promotion mechanism.

The tracked [Archon workflow](../.archon/workflows/agent-orchestrator-definite-sequence.yaml)
calls this Python queue. Its [shell wrapper](../scripts/run_agent_orchestrator_archon.sh)
requires a separately provisioned checkout at `<repo>/archon` and a compatible
Bun/Archon CLI. That root directory is ignored and not supplied by a normal
clone. The [`tools/archon` submodule declaration](../.gitmodules) does not
establish that it is the same runtime or a drop-in replacement.

The wrapper derives `INFO_GEOMETRY_RUNTIME_DIR`, `ARCHON_HOME`, and
`PI_RUNTIME_HOME` from the checkout with environment overrides, then passes
`HOME="$PI_RUNTIME_HOME"` to its child. These are wrapper behaviors, not
requirements to modify a host account. Confirm the prerequisite checkout and
provider configuration before using the wrapper; a provider/authentication
failure is separate from a Lean proof failure.

Native session agent teams, Pi teams, the persistent Hive swarm, and the
Archon/Python queue are separate schedulers. Use the
[native-team protocol](CODEX_AGENT_SWARM_PROTOCOL.md) or
[Pi operations guide](PI_AGENT_TEAMS_OPERATIONS.md) for the chosen runtime.
Do not run competing schedulers against one task or report a queued assignment
as a running worker without checking its state.

## GEPA, observations, and domain-specific routing

GEPA operates on recorded outcomes and candidate profiles. The
[package scripts](../package.json) expose `ai:oracle:record`, `ai:oracle:gepa`,
`ai:oracle:gepa:gate`, and `ai:messages:observe`; inspect their owners and
required inputs before running them. The
[message observer](../tools/infra/gepa_agent_message_observer.py) writes review
evidence. Proposed changes to prompts, SOPs, or workflows remain candidates
until reviewed; they must not silently replace maintained source or acceptance
criteria.

For categorical/tower work, read the
[infrastructure map](CATEGORICAL_INFRASTRUCTURE_MAP.md). For DAG/refactor work,
use the [wire-refactor workflow](../skills/lean-dag-wire-refactor/SKILL.md).
For Souriau/Bost–Connes claims, read the
[transition status](SOURIAU_BOST_CONNES_TRANSITION_STATUS.md). Other domain
routing is in [AGENTS.md](../AGENTS.md#optional-services-and-domain-routing).

## Quality Management System (QMS)

Theorem-bearing work follows [docs/ALCHEMICAL_QMS_SOP.md](ALCHEMICAL_QMS_SOP.md)
(QMS-SOP-ALC-001, v4.1). The SOP enforces role separation between generation
(G-A), audit (A-A), acceptance (QA-A), and orchestration. QMS tooling is
repo-owned under `tools/qms/` — no new network dependencies are introduced.

| Gate | Purpose | Command | Role |
|---|---|---|---|
| 0 | Intake — formal intent envelope | `python3 tools/qms/run_qms.py intent --task-id T --source-text "..." --risk-level R2 ...` | G-A |
| 1 | Owner-first search | `python3 tools/qms/run_qms.py owner-search --task-id T --artifact <file> --query <symbol-or-concept>` | G-A |
| 2 | Artifact static scan; semantic controls remain for independent audit | `python3 tools/qms/run_qms.py generation --task-id T --artifact <file>` | G-A |
| 3 | Sterile compile + audit | `python3 tools/qms/run_qms.py compile --task-id T --artifact <file>` | QA-A |
| 4 | CAPA loop | `python3 tools/qms/run_qms.py capa create --task-id T --finding "..." ...` | Orchestrator |
| 5 | Acceptance | `python3 tools/qms/run_qms.py accept --task-id T --artifact <file> --verdict ACCEPTED ...` | QA-A |
| — | Quick gate (SOP §18) | `python3 tools/qms/run_qms.py quick-gate --task-id T` | QA-A |
| — | CAPA index | `python3 tools/qms/run_qms.py capa-index` | Any |

QMS artifacts are written to `artifacts/qms/<task-id>-{intent_envelope,audit_report,qa}.json`
and `artifacts/qms/capa/`. Gate results record exact commands, outputs, and
remaining debt.

Permitted foundational axioms are `propext`, `Classical.choice`, and
`Quot.sound`. Do not introduce `sorry`, `admit`, custom axioms, `native_decide`,
or vacuous wrappers to obtain acceptance.

## Completion record

Report the checkout revision, changed files, precise theorem or operational
scope, exact commands and results, axiom/placeholder/semantic checks where
applicable, and remaining failures or unrun checks. Preserve relevant report
provenance without committing generated debris indiscriminately. A read-only
documentation audit should say that it inspected source and did not run a
full Lean build or certify optional runtime services.

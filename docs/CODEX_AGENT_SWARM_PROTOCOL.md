# Codex Agent Team Protocol for OpenGauss Work

## Scope and source architecture

This is a Codex adaptation of the repository's TeamAntigravity/OpenGauss
workflow. Its source contract is
`.agents/plugins/opengauss/reference/TOP_DOWN_PROTOCOL.md`, supplemented by
the OpenGauss command skill and trap catalog. The adaptation uses the active
Codex session's collaboration API (`collaboration.spawn_agent`,
`send_message`, `followup_task`, and `wait_agent`). That API coordinates the
current session; it is not a shell command, persistent service, or repository
queue, and a repo script cannot invoke it.

The repository has several distinct, real mechanisms which must not be
collapsed into one claimed runtime:

- **TeamAntigravity protocol:** the three-tier Leader / Orchestrator / Worker
  model and assume-and-recurse proof method described below.
- **Hive is the existing persistent swarm:** `hive_motherbee.py` routes typed
  packet states into role-specific tasks; `hive_arango_queue.py` provides
  leases, worker heartbeats, claims, completion, failure, and requeue; and
  `hive_bee_runner.py` enforces role/task/output authority contracts.
  `hive_swarm.py` runs generator, critic, and Lean formalizer steps in one
  process. Successful Lean proof capture may be fossilized with QMS acceptance
  pending; no in-process model response is treated as an audit. Separate build,
  audit, and promotion workers are workflow roles;
  their separate process or caller-supplied worker labels alone do not prove
  distinct QMS agent instances. The systemd beehive target and installer
  provide a configured activation path; source presence alone does not
  establish that those services are running on this host. Hive is a
  repository-owned persistent workflow, distinct from Codex session agents.
- **Archon/Python theorem queue:** `agent_orchestrator_queue.py` performs its
  local search / optional supplied SymPy / Lean / linter / report steps. It is
  separate from both Hive and Codex collaboration.
- **Vendored Antigravity SDK:** `proofs/antigravity-sdk-python` contains an
  actual subagent API/runtime and round-based examples. `Agent` enables the
  harness `START_SUBAGENT` tool through `CapabilitiesConfig`; the local
  connection tracks child trajectories and completion hooks. The round-based
  examples coordinate independent sessions. This is vendored Google SDK code,
  not the OpenGauss coordinator and it does not start Codex agents.

Treat source files as the executable contract. Protocol documents and prior
`.agents/teamwork*` run records help specify roles and gate panels, but a past
run artifact is not a dispatcher. Likewise, command-shaped functions in
`tools/infra/opengauss_cli.py` must be checked individually; a plan or candidate
helper is not proof execution unless its implementation invokes the relevant
tool and records its result.

## Codex mapping of the TeamAntigravity tiers

1. **Leader (the coordinating Codex agent):** owns the headline theorem,
   global dependency/causal plan, dead-route ledger, and promotion decision.
   It keeps its own context compact, rehydrates from `PLAN.md`, `git status`,
   staged paths, and current owner files after compaction, and never treats
   agent summaries as ground truth.
2. **Orchestrator (the coordinating Codex agent, or a bounded planning turn):**
   derives consumer-minimal child contracts, schedules agent waves, preserves
   sandbox boundaries, and checks source/build evidence. The Codex API does not
   enforce this tier separation automatically; the prompt and coordinator must.
3. **Worker swarm (native Codex agents):** each task is a single bounded leaf:
   source scout, prover/candidate author, refuter, reviewer, or auditor. Give
   each the exact carrier, definitions, hypotheses, owner paths, and read/write
   boundary. Agents return evidence or a proposal; only the coordinator edits
   existing owner files and promotes changes.

The repository's three-tier model is a responsibility split, not a claim that
Codex exposes three special agent types. Use native collaboration agents for
independent work and let the coordinator enforce the protocol.

## Assume-and-recurse proof loop

1. Recover repository/task state from `PLAN.md`, `git status`, staged paths, and
   the current owner source. Search executable code and theorem dependencies.
2. State the headline theorem with its exact carrier, operations, conventions,
   and hypotheses. Draft helper statements from what the parent proof actually
   consumes; apply Anti-T11 consumer-minimal weakening and do not elevate a
   helper's strength without need.
3. Assemble and compile the parent glue against the proposed child contracts
   before assigning proof work. In Codex work, keep unproved contracts in an
   untracked/new scratch proposal or as explicit task text; never commit a
   `sorry` skeleton as a completed theorem.
4. For each nontrivial leaf, pair a prover/candidate author with a concurrent
   refuter. The refuter treats the statement as false or vacuous, checks the
   trap catalog including T16, and seeks counterexamples or missing
   hypotheses. A counterexample or substantive trap finding suspends that
   proof route until the coordinator revises the statement and re-glues it.
5. Use a source scout before creating a replacement abstraction: search Mathlib,
   local declarations, imports, instances, and categorical/operator owners.
6. After candidate work, run independent reviewers/challengers and an auditor.
   For integration-sized changes, add an end-to-end verifier and a separate
   victory audit. Gate-panel agreement is review evidence, never a proof.
7. The coordinator inspects all returned artifacts, applies accepted changes
   to the existing owner, then runs the serial locked Lean build, exact axiom
   audit, semantic/vacuity checks, and required OpenGauss gates. Only observed
   source and tool output can close the task.

Codex-native work waves should be staged around dependencies rather than
launched as an undifferentiated swarm. Independent source scouts and refuters
can run concurrently; child proofs follow after the theorem contract survives
refutation; integration and victory audits follow after the coordinator's
source patch and build.

## Bounded Codex agent roles

1. **Scout / Researcher:** trace actual code and owner definitions, not just
   names/docstrings; return exact paths, declarations, dependencies, and
   existing infrastructure. Read-only.
2. **Prover / candidate author:** work on one supplied child contract. Any code
   proposal goes in a new sandbox file, never an existing owner file. Include
   the exact mathematical context, avoid `sorry`/axiom shortcuts, and report
   compile evidence truthfully.
3. **Refuter / challenger:** independently attack the statement, hypotheses,
   carrier alignment, and proof route. Use T1–T16, construct counterexamples
   where possible, and report a specific stop/revise recommendation. Read-only
   against owner files.
4. **Reviewer / Gate Panel member:** audit one dimension (mathematical scope,
   Lean proof, architecture/dependencies, or QMS honesty) independently. Do not
   rubber-stamp another agent's conclusion. The reviewer must be a different
   agent instance from the artifact author.
5. **Auditor / Victory Auditor:** inspect the final owner diff and recorded
   evidence after build/gates; distinguish a local check from subsystem or
   repository-wide closure. Do not edit or audit work you authored.
6. **Archivist:** coordinator records plan state, exact changed paths and
   declarations, rejected routes, source/build/axiom/gate outputs, and
   remaining debt. Do not stage generated debris or unrelated user changes.

## Codex API limits and Antigravity mechanics

The SDK demonstrates built-in subagent trajectories, independent stateful
sessions, barrier-synchronized rounds, reactive coordination, and lifecycle
hooks. Codex collaboration supplies agent turns and messages, but it does not
itself provide Hive's packet ledger, persistent queue, task leases,
role-authority enforcement, automatic hooks, or OpenGauss acceptance pipeline.
For session work, mirror the role boundaries and staged gates in coordinator
prompts and plan state. For persistent Codex-backed work, the right integration
point is the existing Hive task/packet contracts and workers, with an explicit
Codex execution adapter; do not create a competing queue or imply that
`spawn_agent` invokes Hive/Archon.

Hive's in-process model “auditor” response is a composite self-review, not an
independent agent audit. Likewise, Hive's separate worker process and distinct
`worker_id` labels are not evidence that the QMS non-overlapping G-A, A-A, and
QA-A roles were filled. Use distinct agent instances/contexts for A-A and QA-A;
QA-A must differ from both the author and A-A and rerun the decisive checks.
In `hive_swarm`, “proof fossilized” means the Lean proof capture was stored;
`qms_review.status = pending_external_audit` means QMS acceptance has not been
granted. These states are separate, and only the external A-A/QA-A cycle can
close the latter.

Do not run Hive, Archon, Pi, and manual Codex coordination against the same task
at once. Select one scheduler for that task. Regardless of scheduler, builds
remain single-flight through the repository lock.

## OpenGauss acceptance sequence

1. Read `AGENTS.md`, `docs/CANONICAL_AGENT_PIPELINE.md`,
   `docs/HIVE_AGENT_COMMANDMENTS.md`, `docs/INDEPENDENT_AGENT_AUDIT_SOP.md`,
   `.agents/plugins/opengauss/reference/TOP_DOWN_PROTOCOL.md`, the command
   skill, the trap catalog, and relevant owner sources.
2. Inspect `git status` and preserve unrelated staged and unstaged work.
3. Build consumer-minimal contracts, compile the glue, then assign bounded
   source audits, leaf proofs, and paired refutations. Give every agent the
   explicit context and ownership boundaries.
4. Make the smallest source edit in the owner layer. Reuse categorical and
   operator owners; do not introduce scalar, diagonal, or commuting proxies for
   a noncommutative carrier.
5. Run only preliminary checks needed to make the candidate reviewable; label
   them preliminary and do not treat them as acceptance evidence. Dispatch A-A
   to inspect the exact candidate diff read-only. G-A, the artifact author,
   cannot audit or accept that artifact. Resolve A-A findings and send the
   revised exact diff back to A-A for closure.
6. Once A-A closes the final diff, inspect for active Lean/Lake processes.
   Run builds sequentially through
   `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <target>`.
   Never run `lake clean` or remove build caches.
7. Run the repository's audited OpenGauss screener, strict refute, Gate 4,
   semantic-vacuity checks, relevant audit companion, regression target, and
   declared theorem axiom checks on the A-A-reviewed source. Read each result;
   report warnings instead of claiming a clean result when warnings remain.
   Stage only task-owned paths when the tree already contains unrelated staged
   work.
8. Dispatch QA-A, distinct from both G-A and A-A, to rerun the decisive checks
   against the exact A-A-reviewed diff and verify their outputs. QA-A is not
   permitted to rely on the author's or A-A's check summaries. If QA-A requests
   changes, return the change to A-A, then repeat final verification and QA-A.
9. Report exactly what Lean established and any claims still outside the
    formalized statement, with the separate A-A and QA-A dispositions.

Automated screening, compilation, and the author’s own checks are not
independent audit or acceptance evidence.

## Starting an actual Codex team

In an active Codex conversation, the coordinator calls the native
`collaboration.spawn_agent` tool with a narrow task, role, exact owner paths,
mathematical definitions, child contract, and explicit read/write limits. Pair
each nontrivial prover task with a refuter; use separate reviewer/auditor turns
for the relevant gate. Collect results with `wait_agent`, `send_message`, and
`followup_task`. Inspect every returned artifact against the checked-out source.
The coordinator makes the owner edit, runs or coordinates the locked Lean build
and axiom/QMS gates, and records the distinct A-A and QA-A dispositions. The
coordinator does not substitute its own review for either role; an agent message
alone does not close the task.

There is no `codex swarm` shell command in this repository. For queued local
Researcher/SymPy/Lean/linter/report work, use the separately documented
Archon/Python queue only after checking that its queue and runtime prerequisites
are present. Do not substitute it for the native Codex agent API.

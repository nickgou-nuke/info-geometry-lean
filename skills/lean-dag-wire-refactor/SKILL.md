---
name: lean-dag-wire-refactor
description: Use for info-geometry-lean cleanup work that runs DAG, ArangoDB, LeanTrail, graph-overlay, de Bruijn/hash/WL, and Hodge/causal-cone analyses to find redundant theorem wires, duplicate namespaces, pure forwarding modules, stale dropins, compatibility shims, and duplicate proof surfaces, then refactors them only through Lean-checked owner edits.
---

# Lean DAG Wire Refactor

Use this skill for repository-wide redundancy cleanup in
`/home/goutev/repos/info-geometry-lean`.

Core law:

```text
Graph tools identify candidate wires.
Lean owner files decide truth.
Only kernel-checked source edits count.
```

Hashes, WL classes, Arango paths, critic packets, Hodge cones, and de Bruijn
signatures are evidence for navigation, never proof authority.

## Dirty-State Gate

Before analysis or edits:

```bash
git status --short --branch
git ls-files --others --exclude-standard
```

Rules:

- Do not reset or restore user work unless explicitly requested.
- Do not edit dirty external submodule worktrees unless explicitly targeted.
- Preserve untracked non-artifact source/tool files, or report the boundary.
- Ignore generated `artifacts/` unless the user asks to track reports.
- Stay on `main`; do not create branches unless explicitly requested.

## Evidence Refresh

Refresh only what the task needs. For broad redundancy planning, run the full
evidence stack; for one namespace/module, run the smallest relevant subset.

Core DAG health:

```bash
lake script run dagStatus
lake script run dagRefresh
lake script run dagReports
lake script run dagDoctor
```

Repo-scoped graph overlay:

```bash
.venv-py312/bin/python \
  tools/observability/graph_overlay_toolchain/graph_overlay/scripts/lean_graph_overlay.py \
  lean \
  --out-dir artifacts/graph_overlay/current \
  --filter-prefix InfoGeometry \
  --report-stem infogeometry
```

Arango lossless DAG and algorithms:

```bash
.venv-py312/bin/python tools/infra/materialize_lossless_infotree.py \
  --input-dir artifacts/dag/index \
  --structural-topology artifacts/dag/structural-topology.json \
  --output-dir artifacts/infotree/lossless-dag-current

tools/infra/with_arango_env.sh -- .venv-py312/bin/python \
  tools/infra/arango_layered_ingest.py \
  --input-dir artifacts/infotree/lossless-dag-current \
  --drop-existing \
  --json-out artifacts/infotree/arango-layered-ingest-current.json

tools/infra/with_arango_env.sh -- .venv-py312/bin/python \
  tools/infra/arango_dag_algorithms.py \
  --compute-dominators \
  --wl-limit 7000 \
  --motif-max-nodes 1500 \
  --two-complex-max-nodes 7000 \
  --two-complex-max-edges 200000 \
  --two-complex-cell-limit 10000 \
  --process-flow-limit 100000 \
  --lawful-path-limit 5000 \
  --hodge-sparse-limit 20000 \
  --write \
  --drop-existing \
  --create-named-graph \
  --graph-name arango_dag \
  --json-out artifacts/infotree/arango_dag_algorithms_report.json
```

LeanTrail lanes:

```bash
lake script run leantrailConformance

lake script run leantrailSurgeryPlan \
  --snapshot artifacts/leantrail/graph_snapshot.vacuity.json \
  --json-out artifacts/leantrail/surgery_plan_report.json \
  --vacuum-out artifacts/leantrail/vacuum_packets.jsonl \
  --bridge-out artifacts/leantrail/bridge_packets.jsonl \
  --alignment-out artifacts/leantrail/alignment_packets.jsonl \
  --proof-hole-out artifacts/leantrail/proof_hole_packets.jsonl

lake script run leantrailHolePackets

lake script run leantrailCriticPackets \
  --snapshot artifacts/leantrail/graph_snapshot.vacuity.json \
  --proof-holes artifacts/leantrail/proof_hole_packets.jsonl \
  --bridge-packets artifacts/leantrail/bridge_packets.jsonl \
  --alignment-packets artifacts/leantrail/alignment_packets.jsonl \
  --out artifacts/leantrail/critic_packets.jsonl \
  --json-out artifacts/leantrail/critic_packets_report.json \
  --md-out artifacts/leantrail/critic_packets_report.md \
  --top-n 50

lake script run leantrailCriticPrompts \
  --packets artifacts/leantrail/critic_packets.jsonl \
  --out artifacts/leantrail/critic_prompts.jsonl \
  --json-out artifacts/leantrail/critic_prompts_report.json \
  --md-out artifacts/leantrail/critic_prompts_report.md \
  --limit 200 \
  --top-n 50

lake script run leantrailCriticIngest \
  --snapshot artifacts/leantrail/graph_snapshot.vacuity.json \
  --critic-packets artifacts/leantrail/critic_packets.jsonl \
  --out artifacts/leantrail/graph_snapshot.critic.json \
  --json-out artifacts/leantrail/critic_ingest_report.json
```

If the repo has a shadow-ledger script, run it before any automated contraction
attempt. Otherwise treat `vacuum_packets.jsonl` as review evidence only:

```bash
lake script run leantrailShadowLedger \
  --snapshot artifacts/leantrail/graph_snapshot.vacuity.json \
  --vacuum-packets artifacts/leantrail/vacuum_packets.jsonl \
  --out-approved artifacts/leantrail/shadow_approved_packets.jsonl \
  --out-deferred artifacts/leantrail/shadow_deferred_packets.jsonl \
  --manifest-out artifacts/leantrail/surgery_manifest.json \
  --json-out artifacts/leantrail/shadow_ledger_report.json
```

## Candidate Discovery

Prioritize candidates in this order:

1. `linter.dupNamespace` warnings where an outer namespace repeats a structure
   or nested namespace name.
2. Pure forwarding modules that only restate already-owned declarations.
3. Exact stale dropin/archive copies whose active implementation exists under
   `tools/`, `lean/`, or `lakefile.lean`.
4. Compatibility aliases with no remaining direct imports or only same-module
   usage.
5. Alpha/de Bruijn/hash/WL duplicate declarations whose proof body is merely
   forwarding, projection, readback, or wrapper transport.
6. Critic-packet targets with source-level evidence: witness field packaging,
   `_statement/_sorry` pairs, `readback` sockets, opaque boundaries, or unused
   compatibility modules.
7. Arango/Hodge causal cones whose protected intersections are empty and whose
   owner files show a real forwarding wire.

Never delete or contract a theorem solely because it is graph-isolated,
topology-weak, low fan-out, or hash-duplicated.

## Candidate Dossier

Before editing, create a small mental or written dossier:

```text
candidate:
  name/module:
  class: duplicate_namespace | forwarding_module | stale_dropin | alias_wire | alpha_duplicate
  owner declaration/module:
  graph evidence:
  source evidence:
  protected/API intersections:
  proposed action:
  validation target:
```

Reject the candidate if source evidence is weak, if it crosses a protected/API
boundary, if it is an orphan-genuine theory, or if the action would replace one
carrier structure with another.

## Causal Extraction

For a declaration or module:

```bash
rg -n "<NameOrNamespace>" lean -g '*.lean'
rg -n "import <Module.Path>" lean -g '*.lean'
```

Use Arango only to scope impact:

```aql
FOR c IN arango_dag_components
  FILTER @name IN c.members[*].name OR c.representative == @name
  RETURN c
```

Then inspect raw Lean files before editing.

## Refactor Patterns

### Duplicate Namespace

If a file has:

```lean
namespace A.BridgeName
structure BridgeName ...
namespace BridgeName
```

prefer renaming the owner namespace, not the structure:

```lean
namespace A.Bridge
structure BridgeName ...
namespace BridgeName
```

Search and update fully qualified uses. Do not add compatibility aliases unless
there is a real downstream need.

### Pure Forwarding Module

If a module contains only owner restatements:

```lean
lemma x := Owner.x
theorem y := Owner.y
```

and no external import depends on it, remove the module and remove its umbrella
import. If downstream files import it, update them to import the owner module.

### Stale Dropin Archive

If a dropin directory duplicates active tracked tools:

```bash
git diff --no-index --stat archive/path active/path
```

Remove or quarantine the archive only after verifying active Lake scripts still
run:

```bash
lake script run leantrailSurgeryPlan --help
lake script run leantrailCriticPackets --help
```

### Witness/Carrier Surface

Do not replace one carrier structure with another. Either:

- prove from lower definitions;
- collapse a forwarding theorem to its owner theorem;
- leave explicit closure debt.

## Source-Edit Gate

For automatic or semi-automatic contraction, require all of:

```text
packet_stream = vacuum
action_phase = contract
state = shadow_approved, or certified only for explicit manual debugging
decl_span_kind = top_level_decl
patch_span_kind = decl_body
source_info_kind = original
scc_size = 1
contamination = clean
is_prop = true
fileHash matches
no high-severity unresolved critic packet
```

Deletion is disabled by default. It needs a fresh audit, fresh reachability,
fresh Hodge/cone check, no imports, no references, and explicit user intent.

## Validation Gate

For every Lean edit:

```bash
lake env lean <edited-file>
lake build <target-module>
rg -n "<old-qualified-name>|import <deleted-module>" lean -g '*.lean'
```

For umbrella/import removals, build the umbrella module and at least one known
downstream dependent.

If generated reports change and are tracked, commit them separately from source
refactors. If ignored, do not force-add them unless requested.

## Commit Discipline

Use narrow commits:

```text
refactor(<area>): deduplicate <specific wire>
chore(<tool>): remove stale <specific archive>
```

Before committing:

```bash
git diff --check
git status --short --branch
```

After committing only when requested or when this workflow is already explicitly
in commit/push mode:

```bash
git push origin main
git push upstream main
```

## Report Shape

Final report must list:

- tools run and key counts;
- candidate selected and why it is a real redundant wire;
- exact files changed/deleted;
- Lean/lake validation commands;
- commit hash and push destinations, if committed;
- residual dirty state, especially submodules or untracked user files.

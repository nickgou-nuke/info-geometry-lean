---
name: frontier-proof-compression
description: Use when working inside the InfoGeometry repository on Skynet/OpenClaw-guided proof compression: selecting native structural hotspots, running skynet_v2 and the optimization cycle, replacing vacuous or surrogate theorem surfaces with constructive lemmas, canonicalizing consumer endpoints, and regenerating structural reports to verify real burn-down.
---

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with native Lean 4 proofs is the highest mandate. Treat witness packets, certificate fields, external certificates, assumption interfaces, literature owners, graph edges, and physics analogies as closure debt until discharged by kernel-checked Lean or imported mathlib theorems. Follow docs/CONSTRUCTIVE_CLOSURE_MANDATE.md; never promote anonymous or unformalized sockets as complete.

# Frontier Proof Compression

Use this skill when the task is not just to inspect the DAG, but to reduce theorem-surface debt by replacing repeated assumption transport, surrogate closures, or vacuous wrappers with constructive Lean proofs.

## First Read

Read these first:

1. `skills/info-geometry-repo/SKILL.md`
2. `reports/dag/openclaw-targets.md`
3. `reports/dag/structural-hotspots.md`
4. `reports/dag/replacement-frontier.md` (ranked by replacement feasibility, cross-references depth and vacuity)

Then read only the exact frontier/module files you need.

## Trigger Conditions

Use this skill when the user asks for any of these:
- continue the current frontier attack
- run `skynet_v2` or the optimization cycle
- auto-proof or auto-optimize a frontier slice
- replace vacuous/surrogate theorem surfaces with constructive lemmas
- canonicalize a repeated assumption-transport chain
- compress the theory by thinning synthesis/consumer modules

Do not use this skill for generic Lean debugging, one-off theorem proving without frontier context, or pure DAG reporting.

## Hard Goal

The goal is not to add wrappers. The goal is to remove repeated assumption transport.

Count progress only when at least one of these happens:
- a surrogate theorem disappears
- a downstream theorem loses intermediate assumptions
- a consumer module stops reconstructing a ladder that already exists upstream
- anti-bleed pressure or hotspot rank drops after regeneration

Treat these as non-progress unless they immediately delete debt elsewhere:
- alias theorems
- definitional restatements
- assumption-local packaging
- synthesis-local replay of an upstream constructive chain

## Canonical Loop

1. Read the current target from `reports/dag/openclaw-targets.md`.
2. If graph coverage still has uncovered debt, fix that first.
3. Otherwise take the top structural hotspot and use its recommended seed.
4. Run `skynet_v2` on that seed with reverse walk.
5. Run one optimization cycle from the resulting frontier JSON.
6. Inspect the top frontier item and identify the repeated transport chain.
7. Add the smallest constructive lemma family that collapses that chain at the latest useful point.
8. Rewrite downstream consumers to call the new endpoint instead of replaying the chain.
9. Run focused locked builds for the touched Lean modules.
10. Regenerate source-sink compression, structural anti-bleed, and OpenClaw targets.
11. Accept the patch only if structural pressure or theorem-surface debt actually falls.

## Preferred Theorem Shape

Prefer theorem tiers of this form:
- constructive bridge tier: `..._of_<real source data>`
- consumer tier: `..._of_<canonical phase/invariant>`

The constructive bridge should live as close as possible to the true source lane.
The consumer theorem should live in the hotspot file that needs the consequence.

Avoid:
- proving consumer-local transport facts in synthesis files
- introducing a new hub module when an existing proof-producing layer already owns the chain
- adding more `_of_normal` or `_of_commutes` wrappers if those assumptions should no longer be carried downstream

## Current Structural Policy

Use the current trust order:
1. `artifacts/dag/index/meta.json` (verify `schemaVersion` ≥ 2 and timestamp is recent)
2. `artifacts/dag/full_graph.json`
3. `artifacts/dag/structural-topology.json`
4. `artifacts/dag/source-sink-bipartite.json`
5. `reports/dag/structural-hotspots.md`
6. `reports/dag/openclaw-targets.md`

OpenClaw is now a thin selector:
- uncovered graph debt first
- otherwise native structural hotspots only

## Core Commands

Frontier extraction:

```bash
python3 tools/skynet_v2.py \
  --seed "<seed>" \
  --walk reverse \
  --json-out reports/dag/skynet-v2-frontier-<slug>.json \
  --md-out reports/dag/skynet-v2-frontier-<slug>.md
```

Quarantine cycle:

```bash
python3 tools/run_optimization_cycle.py \
  --frontier-json reports/dag/skynet-v2-frontier-<slug>.json \
  --frontier-index 0 \
  --fresh-worktree
```

Focused verification:

```bash
python3 tools/infra/run_locked_lake_build.py <Module.Name>
```

Regeneration:

```bash
# Refresh the DAG (incremental; skips if oleans unchanged)
python3 tools/infra/refresh_decl_graph.py
# Use --force to bypass the incremental skip
python3 tools/infra/refresh_decl_graph.py --force

python3 tools/infra/generate_source_sink_compression.py

python3 tools/infra/check_bipartite_bleed.py

python3 tools/infra/generate_causal_report.py \
  --out reports/dag/true-root-order.md \
  --json-out reports/dag/true-root-order.json

python3 tools/infra/select_openclaw_target.py \
  --input reports/dag/true-root-order.json \
  --structural-hotspots reports/dag/structural-hotspots.json \
  --json-out reports/dag/openclaw-targets.json \
  --md-out reports/dag/openclaw-targets.md

python3 tools/infra/generate_replacement_frontier.py
```

## Acceptance Test

Before closing a strike, verify all of these:
- touched Lean modules build
- regenerated structural hotspot report still parses
- OpenClaw target selection succeeds
- the patch created a constructive endpoint or removed downstream assumption carry
- the change can be explained as path compression, not interface decoration

## Output Style

When reporting results, say:
- which theorem family was added or rewritten
- which repeated transport chain it replaced
- which hotspot/module was affected
- whether the regeneration changed target order or anti-bleed pressure

If the numbers did not improve, say so plainly and do not claim burn-down.

## UTMOST MANDATE: Native Lean proof closure over witness/certificate scaffolding

Effective immediately, replacing witness-gated and external-certificate leftovers with native Lean proofs is the top-priority mandate.

Policy requirements:
- Witness packets, certificate fields, external certificates, and assumption interfaces are temporary scaffolding only.
- They are not final mathematical closure and not promotion authority.
- Every promoted proposition must be discharged by native Lean derivation chains in-repo (owner -> translator -> mathlib-rooted proof path).
- When a native Lean proof is not yet available, the gap must be recorded explicitly as open closure debt; do not package it as complete.
- **Do not “resolve” debt with wording.** Progress must be structural, not just textual.
- **Do not remove debt labels** unless there is a native explicit Lean proof term checked by the kernel closing that specific debt.
- **Real progress** = replacing certificate/witness fields with theorem-backed native derivations.

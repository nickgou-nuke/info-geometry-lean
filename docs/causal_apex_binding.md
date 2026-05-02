# Causal Apex And Binding Note

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This file is a diagnostic note for graph analysis over exported repository
artifacts.

It is not a proof source, not an ontology file, and not a substitute for code
inspection. Lean source, repository DAG reports, and the native audit remain
primary.

## What this note is for

The repo now has enough real trunks and branch junctions that graph diagnostics
can be useful, but only as a secondary lens.

This note records the intended interpretation of:

- apex candidates
- binding witnesses
- shell depth
- role-weighted structural mass

over the SCC-condensed dependency DAG used by the maintained graph tooling.

## Current tooling anchor

The relevant maintained tool is:

- `tools/infra/causal_cone_spectrum.py`

Generated graph artifacts and derived reports remain the operational surfaces:

- `reports/dag/`
- `artifacts/dag/`
- `docs/auto/index.md`

This note should be read as the diagnostic theory behind those surfaces, not as
an authority on the math itself.

## Base graph object

Use the SCC-condensed declaration graph, not the raw declaration graph, as the
base object for causal order.

Let:

- `G_raw` be the declaration dependency graph
- `Cond(G_raw)` be its SCC condensation DAG
- `C` be the causal orientation of that DAG, where `x -> y` means `y` depends
  directly on `x`

Only this condensed DAG should be used for apex and binding analysis.

## Causal order and shells

For vertices `u, v` in `C`:

- `u <= v` means there is a directed path `u ->* v`

Interpretation:

- `u` is causally upstream of `v`
- `v` depends on `u`

For a node `a`, define:

- `Past(a)` as the upstream cone
- `Desc(a)` as the downstream cone

Past shells are defined by directed causal distance:

- `Shell_k(a) := {u in Past(a) | dist_C(u, a) = k}`

This remains the right way to speak about causal depth in the repo graph.

## Role overlay

The role overlay is still useful, but only as a maintained classifier or
diagnostic overlay, not as a theorem source.

Current role vocabulary remains:

- `owner`
- `translator`
- `coherence`
- `wrapper`
- `capstone`

The point is to distinguish genuine branch junctions from decorative sinks or
wrapper-heavy hubs.

## Binding witness

A binding witness should still be read as a coherence-like node in the upstream
cone whose support genuinely depends on multiple distinct upstream role classes.

That is the correct diagnostic idea, but the full essentiality test is still
not fully implemented. The maintained tooling currently uses a local proxy.

So the current repository status is:

- diagnostic concept: valid and useful
- full formal structural-ablation test: still not implemented

## Apex mass

Role-weighted downstream influence still makes sense as a diagnostic score, but
it must not be confused with mathematical authority.

The current use case is modest:

- detect structurally important junctions
- distinguish load-bearing coherence files from old hubs
- spot fragile thin corridors or wrapper inflation

This is especially useful now that the repo has a real corrected phase-space
trunk plus multiple adjacent branches.

## Current architectural reading

If used today, this overlay should help diagnose:

- the corrected phase-space generalized-metric trunk
- the polarized / recomposition junction
- the KKT / conformal / Weyl branch point
- the count/projective trunk and whether it truly meets the main trunk at the
  polarized carrier

It should not be used to override code-level ownership or theorem-level truth.

## Non-goals

This note is not:

- a physical interpretation layer
- a theorem about declaration meaning
- a replacement for direct code reading
- a license to infer math from graph centrality

## Validation standard

Keep this overlay only if it has diagnostic discrimination beyond simple
centrality statistics.

At minimum it should help separate:

- semantic roots from compatibility scaffolds
- genuine coherence files from wrapper-heavy accumulators
- stable branch junctions from temporary frontier spikes

If it stops doing that, it should be demoted further or removed.

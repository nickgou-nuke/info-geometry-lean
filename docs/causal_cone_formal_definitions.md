# Causal Cone: Formal Definitions

This file records the formal graph definitions behind the causal-cone tooling.

It is a diagnostic and tooling note, not a theorem source for the mathematics in
`lean/InfoGeometry/`.

## Base object

All definitions are taken on the SCC-condensed dependency DAG.

Let:

- `G_raw` be the declaration dependency graph;
- `Cond(G_raw)` be its SCC condensation DAG; and
- `C` be the causal orientation where `u -> v` means `v` depends on `u`.

This remains the correct base object because SCC condensation removes cycles at
the graph-analysis level.

## Core definitions

For nodes `u, v` in `C`:

- `u <= v` means there is a directed path `u ->* v`

For an apex candidate `a`:

- `Past(a)` is the upstream cone
- `Desc(a)` is the downstream cone

Past shells are defined by directed distance:

- `Shell_k(a) := {u in Past(a) | dist_C(u, a) = k}`

This remains the correct formalization for shell-based analysis in the current
tooling.

## Current tooling map

The maintained implementation surfaces are:

- `tools/infra/causal_cone_spectrum.py`
- `lean/DAG/SCC.lean`
- exported DAG artifacts under `artifacts/dag/`

This file should stay aligned with those surfaces, not drift into a separate
mathematical story.

## Role overlay

The current role overlay used by diagnostics remains:

- `owner`
- `translator`
- `coherence`
- `wrapper`
- `capstone`

This is still a diagnostic overlay, not theorem-level ontology.

## Binding witnesses

A binding witness remains a coherence-like node in the upstream cone whose
support genuinely draws from distinct upstream role classes.

Current implementation status:

- local proxy: implemented in `tools/infra/causal_cone_spectrum.py`
- full essentiality / ablation test: still not implemented

That distinction should remain explicit.

## Mass and boundary

Role-weighted downstream influence, shell position, and boundary weakness are
still valid diagnostic ideas, but they should remain diagnostic quantities only.

Their present job is to help distinguish:

- semantic roots
- real branch junctions
- wrapper-heavy hubs
- fragile frontier nodes

They are not semantic truth values.

## Current validation standard

Keep this formal overlay only if it helps recover the present architectural
facts better than naive graph centrality:

- the corrected phase-space trunk;
- the polarized/recomposition junction;
- the KKT/conformal/Weyl branch point; and
- the count/projective trunk and its meeting behavior.

If it stops doing that, it should be simplified or removed.

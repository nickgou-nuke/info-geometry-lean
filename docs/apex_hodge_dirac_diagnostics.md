# Apex-Local Hodge-Dirac Diagnostics

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

This note records a spectral diagnostic overlay for local repository
neighborhoods.

It is not a theorem about the mathematics formalized in the repo. It is a
secondary graph-analysis tool for detecting architectural entanglement,
compression, and fragility in apex-local neighborhoods.

## Current tooling anchor

The relevant maintained artifacts are:

- `lean/DAG/GraphHodge.lean`
- `tools/infra/graph_hodge_spectrum.py`
- `tools/infra/causal_cone_spectrum.py`
- `tools/infra/apex_defect_profile.py`

This note should be read as the interpretation layer for that diagnostic
tooling.

## Current doctrine

The spectral carrier is still:

1. choose an apex;
2. take its SCC-condensed causal past cone;
3. enrich the local neighborhood to a simplicial complex; and
4. study local Hodge / Hodge-Dirac modes there.

The purpose is not to certify “importance.” It is to detect:

- thin shell transitions,
- artificial circulation,
- localized near-zero bottlenecks, and
- harmonic holes that may correspond to missing comparison or coherence cells.

## Current interpretation

The main signals remain:

- harmonic modes as candidate coherence gaps;
- localized near-zero modes as bottlenecks or replacement fragility;
- strong circulation as evidence of facade routing or local abstraction loops.

These are diagnostic hypotheses only. They must be checked against source.

## Current repository use

In the present repo state, this overlay is most useful for checking whether:

- the corrected phase-space trunk has clean local factorization into chirality,
  polarized, recomposition, and KKT branches;
- the conformal/Weyl packet still carries unresolved local circulation;
- count/projective and phase-space branches meet by theorem or only by graph
  proximity.

## Limits

- The spectral overlay does not prove missing mathematics.
- Signals depend on the chosen local carrier and simplex completion rule.
- The graph view is always downstream of actual Lean source.

If the spectral picture conflicts with direct code reading, the source wins.

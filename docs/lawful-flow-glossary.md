# Lawful Flow Glossary

This glossary is a diagnostic vocabulary for repository graph and architecture
analysis.

It is not a theorem source. It does not override Lean ownership or proof
content. Use it only when reading generated graph reports, audit output, or
structural diagnostics.

## Purpose

The repo now has several real trunks and branch junctions. This glossary gives
names to good and bad flow patterns in that dependency graph:

- lawful flow through explicit owners and bridges;
- weak flow through wrappers or remote attachment; and
- unresolved comparison debt where two corridors remain merely compatible.

It is mainly useful when reading:

- `reports/dag/`
- `artifacts/dag/`
- `tools/infra/causal_cone_spectrum.py`

## Boundary tags

Boundary tags classify where a declaration or file sits in the architectural
flow.

### `internal`

- Meaning: the construction stays within one local architectural region.
- Use when: the essential support is local and does not require an interface
  crossing.
- Do not use when: the declaration only looks local but is actually governed by
  a remote bridge theorem.

### `localInterface`

- Meaning: the construction crosses one nearby interface through a sanctioned
  local mediator.
- Use when: there is a single local bridge or translator and the factorization
  is explicit.
- Do not use when: the declaration jumps across regimes directly.

### `bridge`

- Meaning: the primary role is transport across regimes or representations.
- Use when: the declaration materially moves structure from one packet to
  another.
- Do not use when: the theorem only mentions both sides without mediating
  between them.

### `capstone`

- Meaning: the declaration aggregates or summarizes existing flows.
- Use when: it closes a region without introducing a new transport mechanism.
- Do not use when: it introduces new remote structure under a summarizing name.

### `mixed`

- Meaning: more than one boundary reading remains live.
- Use when: the evidence supports incompatible readings and none dominates.

### `unclear`

- Meaning: the exporter or analyst does not yet have enough evidence.
- Use when: classification would otherwise be guesswork.

## Defect tags

Defect tags are local diagnostics. They are not global verdicts on whether the
mathematics is worthwhile.

### `remoteAttachment`

- Meaning: an essential support is taken from a remote region without a local
  mediator.
- Typical sign: a file or theorem is governed by a faraway packet instead of an
  adjacent bridge.

### `failedLocalFactorization`

- Meaning: the construction looks like it should factor through a local bridge,
  but no such bridge is present.
- Typical sign: a large feature jump with no nearby translator.

### `unresolvedComparison`

- Meaning: two live derivation paths appear to carry the same content, but no
  comparison theorem has been provided.
- Typical sign: explicit identification hypotheses that should eventually become
  generated theorems.

### `illicitBoundaryCrossing`

- Meaning: a regime change occurs without a licensed bridge pattern.
- Typical sign: direct use of a remote packet where the architecture expects a
  local corridor.

### `mixedPolarity`

- Meaning: competing directional or regime traces coexist without a stabilizing
  comparison or pairing.

### `regressiveFlow`

- Meaning: the support pattern runs against the intended local causal
  orientation.
- Typical sign: a crown-level theorem acting as a semantic source.

### `typeOnlySupport`

- Meaning: only type-level carriage is visible where value-level transport was
  expected.
- Status: reserved diagnostic; not a current primary signal.

### `boundaryBypass`

- Meaning: a large cross-layer jump occurs without the expected local mediator
  chain.

### `unclearPolarity`

- Meaning: the orientation of the transport cannot yet be inferred reliably.

## Current repository reading

In the present repo state, this vocabulary is most useful for diagnosing:

- whether the corrected phase-space trunk really feeds polarized and
  recomposition branches;
- whether Weyl is fed by the conformal/KKT trunk or only shares scalar labels;
- whether count/projective meets the main trunk at polarization by theorem or
  only by adjacency; and
- whether old split-tower or scaffold files are still being used as roots.

## Policy

- Boundary tags classify structure; they are not praise or blame.
- Defect tags mark local structural debt; they are not rejection criteria by
  themselves.
- Code and theorem content remain primary.
- If a diagnosis conflicts with direct source reading, the source wins.

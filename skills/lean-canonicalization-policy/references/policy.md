# Lean Canonicalization Policy Reference

## Goal

Turn Lean files into a canonical library surface:
- one concept, one owner
- one theorem surface, one semantic role
- no fake public interfaces over lower proofs

## Semantic Classification

Every public declaration should be treated as one of:
- `constructive_endpoint`: proves a real invariant or builds a real witness from lower data
- `bridge_identification`: identifies two genuinely different presentations of the same object
- `transport_lemma`: moves a fact across an existing bridge or change of presentation
- `orientation_wrapper`: rewrite orientation, projection, conjunction, iff-packaging, or direct pass-through
- `scaffold`: existential/specification packaging, readiness shell, or convenience state bundle
- `capstone_consumer`: consumes lower endpoints into a higher presentation but does not introduce new low-level math

Only the first two should normally remain public in low or middle layers.

## DO NOT DO

1. Do not expose wrappers as if they were endpoints.
2. Do not keep carrier, bridge, and capstone mathematics in the same file when ownership can be separated.
3. Do not define absolute log-potential on a wide nonnegative ontology; keep wide relative/AE layers separate from strict-positive pointwise layers.
4. Do not introduce a new quotient, gauge, or state language if the repo already has one at a lower level.
5. Do not use graph hotspots alone to choose cuts.
6. Do not delete valid math merely because a file is hot; split first, internalize wrappers second, delete only pure duplication.
7. Do not let umbrella files become theorem owners.
8. Do not treat assumption repackaging as theorem progress.

## Preferred File Roles

### Substrate
Defines objects, structures, and the lowest-level laws.

### Bridge
Identifies two representations or presentations.

### Representation
Specializes a lower substrate into a concrete model.

### Capstone
Consumes lower endpoints and builds higher consequences.

A file should have one dominant role. If it does not, split it.

## Mathlib-Derived Norms

These are the norms to imitate structurally:
- small, self-contained changes
- minimal imports
- curated roots; avoid bucket imports at low levels
- declarations in the lowest natural file
- clear module docstrings and implementation notes
- names that describe what the declaration really proves
- explicit moves/deletions when reorganizing public surfaces

## Graph Policy

Use the maintained reports in this order:
1. direct file analysis
2. narrow builds
3. semantic quotient
4. projection coloring
5. structural hotspots/fibers for the next target

Interpretation:
- `constructive_core` means the file is probably a trunk, not a shell
- `shell_heavy` means the public surface is overstated
- `monochrome` in projection coloring means safe ownership split candidate
- `braided` means stop and inspect semantics before splitting

## Refactor Checklist

Before editing:
- identify the lowest owner
- identify direct consumers
- mark wrappers that can become `private`

During editing:
- preserve theorem names by preserving namespace
- move code down before deleting aliases
- keep umbrella files as imports only

After editing:
- build the split owner files
- build obvious consumers
- rerun maintained DAG pipeline only after code is stable
- read semantic quotient and projection coloring before the next cut

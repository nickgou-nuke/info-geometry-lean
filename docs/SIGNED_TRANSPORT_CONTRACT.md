# Signed Peirce transport contract

## Carrier and conventions

The generic maps are endomorphisms on the full associative algebra `A`,
represented as `Module.End R A`; the multiplication of `A` is not assumed
commutative. Finite metric results specialize to `Matrix n n ℝ` and use its
native transpose and trace. Peirce corners and the idempotent reflection are
reused from the current repository owners.

For elements `a b : A`, the symmetric and signed transports are ordered
maps built from `a*x*b` and `b*x*a`. Their composition and commutator
identities retain both sandwich terms. The Lean theorem statements and their
hypotheses in `SignedBoundaryTransport`, `PeirceSignedTransport`, and
`SignedTransportMetric` are authoritative; this note does not strengthen
them to positivity, complete positivity, or centrality on all of `A`.

## Scope boundaries

- A symmetric product centralizing its two generators does not imply it is
  central in the ambient matrix algebra.
- Algebraic reciprocal-pair identities do not imply periodic real-time
  motion.
- The finite trace pairing is not an infinite-dimensional completion or a
  Hodge decomposition theorem.
- The order file records explicit prerequisite sets; it is not an extracted
  complete declaration graph or a claim of physical causality.

## Verification

The selected Lean closure for PR #250 was built successfully using
`tools/infra/run_locked_lake_build.py` under the shared lock. The named
signed-transport modules were among the selected targets. The separate native
axiom audit covered only the seven owners enumerated by
`LieJordanPeirceAudit`; see `REAL_GRADED_BOUNDARY_CONTRACT.md` for its exact
counts and scope. Workflow scripts have been updated to target the locally
named `LieJordanGradedDifferential` module while preserving the existing
matrix-specific `PeirceGradedDifferential` owner.

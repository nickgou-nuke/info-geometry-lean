# Candidate source-semantic review 06: projector elaboration repair

Reviewer: /root/graded_unroll_intake.

Scope: independent source-only review. The full candidate and its exact diff
against the previously reviewed integrated projector source were read.
No mathematical source edits, Lean/Lake execution, tests, or GitHub operations
were performed by this reviewer.

## Exact identities

- Candidate:
  /workspace/scratch/9009f3c86480/candidates/graded_unroll/projector/Cl11GradedProjectorDefects.lean
- Candidate SHA-256:
  **8a8d44df4745fe9de2ee5e9552efe433aeba46502901274022227a1216c90b2e**
- Candidate length: 303 lines.
- Comparison source: the projector owner at repository commit 347f02a57.
- Comparison SHA-256:
  e201293de9f1bb81c22a6d468dcb1f60591409d25e8a945f03c33e37d769bc20
- Comparison length: 280 lines.

## Verdict

**No mathematical or source-semantic blocker found.**
The changes preserve the previously reviewed theorem contracts, carriers,
ordered products, and defect values. They are proof elaboration changes.
This verdict does not assert successful compilation.

## Reviewed changes

### Distinct-index polar identity

The private polar-form lemma retains its hypothesis i ≠ j. After finite case
splitting, equal-index branches now close explicitly using that contradictory
hypothesis. The remaining distinct-index branches still evaluate the actual
weighted quadratic form and its polar form.

This does not introduce a vacuous replacement for the theorem: admissible
distinct-index cases remain and are addressed by their concrete quadratic-form
calculation. The resulting Clifford anticommutation statement is unchanged.

### Typed vacuum index

The initial zero is now explicitly typed as Fin 1. Unfolding the native
recursive Idx 3 gives ((Fin 1 × Fin 2) × Fin 2) × Fin 2, so this is exactly the
same all-zero coordinate in the eight-dimensional three-site spinor module.
No coordinate is removed or replaced and no new representation is introduced.

### Explicit matrix-entry goals

The three represented-word evaluations now expose the native matrix index
type and expand matrix multiplication and addition before normalization.
They preserve respectively:

- The ordered pair (1+e₀)(1+e₁), whose vacuum entry is one.
- The ordered triple (1+e₀)(1+e₁)(1+e₂), whose vacuum entry is one.
- The middle word (1+e₀)e₁(1+e₂), whose vacuum entry is zero.

Expansion into finite sums is the definition of matrix multiplication; it
does not replace ordered matrix products with products of diagonal entries.
The Jordan–Wigner map remains the existing genuine algebra homomorphism.
Entry evaluation remains only a separating function, with no multiplicativity
or representation-injectivity assumption.

All downstream defects retain their previous values, including −1/32 for
the normalized three-site quarter-scaling defect and −1/8 for both ordinary
idempotence defects. The final site-projection noncommutativity theorem is
unchanged.

## Acceptance boundary

This review closes the source-semantic assessment of the listed repair
candidate only. It does not supersede any failed prior execution, certify
the integrated file before an exact byte comparison, authenticate a successor
remote run, or establish an axiom footprint. Exact-source compilation and the
owned-declaration audit remain separate acceptance requirements.

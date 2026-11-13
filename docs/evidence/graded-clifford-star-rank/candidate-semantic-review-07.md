# Candidate source-semantic review 07: typed readout binding

Reviewer: /root/graded_unroll_intake.

Scope: independent read-only differential review. No mathematical source edits,
Lean/Lake execution, tests, or GitHub operations were performed.

## Exact source identities

Integrated owner:
/workspace/scratch/9009f3c86480/graded-unroll-extension/lean/InfoGeometry/Clifford/Cl11GradedProjectorDefects.lean

- Reviewed SHA-256:
  **cf582a853fc7c4e2f64627d36aa1a951d0c77fae590f2d4b88f180e9b245943e**
- Length: 309 lines.
- Local history revision containing these owner bytes:
  d1cfb307343b4238e3114c43f920c9a5cde927f0.
- Prior reviewed SHA-256:
  8a8d44df4745fe9de2ee5e9552efe433aeba46502901274022227a1216c90b2e.
- Immutable local comparison revision:
  baa571872bde38d4a62c0e24e4b01b9e2c93ead5.

The scratch candidate already matched the current integrated source, so the
previous snapshot was recovered read-only from local Git history and its SHA
was checked before constructing the complete byte diff.

## Verdict

**No source-semantic blocker found.** The complete diff consists only of the
three explicitly typed local matrix-family bindings, their use in the existing
ordered matrix expressions, and unfolding those bindings during normalization.

In each readout, e is defined to be jwMajoranaPlus 3 with codomain

\[
\operatorname{Matrix}
 \big(((\operatorname{Fin}1\times\operatorname{Fin}2)
            \times\operatorname{Fin}2)\times\operatorname{Fin}2\big)
 \big(((\operatorname{Fin}1\times\operatorname{Fin}2)
            \times\operatorname{Fin}2)\times\operatorname{Fin}2\big)
 \mathbb R.
\]

This expands the same native Idx 3 carrier with eight coordinates. It does not
construct a substitute representation, alter a generator, or reduce the
operator algebra to scalar/diagonal data.

The pair, triple, and middle-word products retain their order. Their vacuum
values remain 1, 1, and 0. All theorem statements, assumptions, and downstream
defect values remain unchanged, including the normalized −1/32 counterexample.

The local binding supplies explicit carrier information for elaboration of
addition and multiplication; it adds no mathematical hypothesis or proof of
the desired result as data.

## Acceptance boundary

This is source-only acceptance of the listed differential change. The reported
prior HAdd carrier errors and the pending successor CI run are execution
matters. This review neither certifies that the errors are resolved by the
compiler nor asserts a successful run, an axiom footprint, or remote
commit/tree provenance.

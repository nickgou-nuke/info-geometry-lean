# Finite matrix stages inside the corrected Cuntz quotient

The constructive step after the core projection is an injective
star-algebra map from each native bitword matrix stage into
`ComplexStarCuntzAlg Bool`. The element map already exists as
`complexStarFiniteStageElement`; it is proved multiplicative and unital
inside the quotient, not inferred from unproved faithfulness of the full
boundary representation.

`CuntzComplexStarBinaryCoreMatrixUnits` reuses the quotient prefix reduction
and partition relation to prove equal-length cancellation, matrix-unit
multiplication, star reversal, right-extension refinement, and the finite
diagonal partition of unity. The existing `list_ofFn_extendBitWord` theorem
is made public without changing its proof, so the extension convention is
reused rather than reconstructed.

`CuntzComplexStarFiniteStageHom` packages the existing element map as a native
linear map and star-algebra homomorphism. Only injectivity uses the already
proved finite matrix representation faithfulness. This does not require or
assert faithfulness of the full Cuntz boundary representation.

For successor compatibility the source owner is
`GenuineMatrixStageMorphism.bondFun_eq_dyadicMatrixEmbedding`: it explicitly
identifies the coherent right-extension bond with a sum of extended matrix
units. Do not replace it with `bitWordDyadicStarEmbedding` without an additional
identification theorem: that other embedding uses an arbitrary `Fintype.equivFin`
index choice, whereas the product-density construction uses the recursive
`bitWordFinPowTwoEquiv`.

The locked `CuntzComplexStarFiniteStageAudit` build passed (9396 jobs).
Its 14 selected declaration reports have transitive axiom union exactly
`[propext, Classical.choice, Quot.sound]`. The four new Lean modules passed
the strict OpenGauss screen with zero traps and produced no compiler warnings.
The independent mathematical review passed. Independent QA reran the locked
audit successfully (9396 jobs, exit 0) and accepted this limited scope.
QA confirmed all 14 reports and zero warnings in the scoped owners; its
721 warnings were dependency-source warnings and package notices.
Logs: `/tmp/cuntz-finite-stage-audit.log` and `/tmp/cuntz-finite-stage-qa.log`.

A direct-limit embedding, its exact core range,
positivity of degree-zero extraction, and full KMS remain further obligations.

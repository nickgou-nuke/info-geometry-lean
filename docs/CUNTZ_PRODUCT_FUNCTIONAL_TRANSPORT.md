# Product functional on the corrected Cuntz quotient

Contract: use the proved injective colimit map with exact core image to obtain
a native linear equivalence from the existing matrix colimit to the existing
equal-length word core. Compose its inverse with the degree-zero projection.
This gives a linear retraction from the corrected quotient to the colimit,
with quotient image exactly the existing projection, preserving one and star.

Compose the retraction with `MatrixStageProductDensity.productFunctional`.
Prove normalization, star preservation, and its exact restriction to the
colimit embedding. Positivity on embedded star-squares follows from the
existing positive product functional. The separate homogeneous-component
argument below proves positivity on arbitrary quotient star-squares;
it is not inferred from the linear retraction alone. The uniform functional's
full algebraic KMS identity is now proved in `CuntzComplexStarAlgebraicKMS`;
see `CUNTZ_QUOTIENT_ALGEBRAIC_KMS_CONTRACT.md` for its verification and scope.

Owners: `CuntzComplexStarColimitCoreRange.range_quotientAlgHom`,
`CuntzComplexStarColimitEmbedding.quotientHom_injective`,
`CuntzComplexStarBinaryCoreProjection.projection_*`, and `MatrixProductState`.
The core is a submodule of the actual quotient; no scalar surrogate is used.

Full positivity route: extract each integer-degree coefficient of `delta`;
prove it homogeneous and that star reverses degree. Native monoid-algebra
convolution at zero then expresses projection of a star-square as the finite
sum of the component star-squares. For nonnegative degree, insert the finite
word partition to obtain core squares. For negative degree, prepend one word
isometry to obtain a single core square. Apply the already transported core
positivity termwise. This is finite algebraic positivity, without analytic
averaging or a new star instance on the graded carrier.

`quotientProductFunctional_nonneg` proves ComplexOrder nonnegativity for
every element of `ComplexStarCuntzAlg Bool`, for real nonnegative letter
weights summing to one. No core-membership restriction remains on the input.
This is a positive algebraic functional; continuity and completion are not
asserted.

The parent locked audit passed (9417 jobs, exit 0); 27 selected declarations
have only standard foundational axioms. All six new Lean owners passed the
strict OpenGauss screen with zero traps. Independent mathematical review
accepted the full positivity proof. Independent QA accepted this scope after
its own locked build (9417 jobs, exit 0), confirming all 27 reports have
axiom union exactly `[propext, Classical.choice, Quot.sound]` and zero warnings
in the six new owners. The remaining 734 warnings were dependency-source
warnings and package notices.
Logs: `/tmp/cuntz-product-audit.log` and `/tmp/cuntz-product-qa.log`.

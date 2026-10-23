# Zorn Peirce intake: native theorem contract

Source: the user's Zorn/Günaydin–Gürsey note in this thread. Its multiplication
matches `InfoGeometry.Algebra.ZornVectorMatrix.mul` over a commutative ring.
Reuse that carrier, `ZornVec3`, `U`, `V`, `E11`, `E22`, `conj`, and `associator`.
Do not install an associative ring instance or introduce another vector carrier.

The native owner already proves norm composition, conjugate-norm identities,
the three alternative laws, all cyclic basis products, mixed basis products,
and `associator_U_zero_U_one_U_two = sub E22 E11`. `ZornAlternativeLaws`
proves Moufang identities. The submitted mixed-color witness instead vanishes:
`associator (U 0) (U 1) (V 2) = zero`.

The constructive repair is a reusable mixed-vector identity on the native
carrier. Writing `upper u = offDiagonal u 0` and `lower w = offDiagonal 0 w`
only as mathematical shorthand, the target is

`[upper u, upper v, lower w] = upper ((v·w)u - (u·w)v)`.

Its basis specialization gives the vanishing submitted example; it also
characterizes exactly when this mixed associator vanishes. Conjugation swaps
the diagonal entries, hence exchanges E11/E22; these are not self-adjoint MP
support projections for this conjugation over a nontrivial ring. No new MP
predicate on the nonassociative carrier is introduced. The associative CAR
replacement already lives in `ZornLeftCAR` (`Module.End ℝ Z`) and its positive
adjoint identity is in `ZornCARAdjoint`. These maps are linear and preserve the
proved anticommutators, not arbitrary element multiplication.

Search: recursive owner searches across `lean/**/*.lean` for Zorn/split-octonion
carriers, associators, Peirce products, conjugation and CAR; read
`ZornVectorMatrix`, `ZornAlternativeLaws`, `ZornDerivationBridge`,
`ZornPinorReconstruction`, `ZornLeftCAR`, `ZornCARAdjoint`, and the mixed-slot
formula in `Canonical/ZornAssociatorDerivationCurvatureBridge`. The latter uses
a different carrier and slot order, not a theorem on this native mixed triple.

Real signature (4,4), historical attribution, physical color/SUSY interpretation,
and an associative supercolor structure are not consequences of the new lemmas.
Parent kernel compilation has passed for these four lemmas. Independent
acceptance is tracked with the signed-basis continuation below.

## Signed-basis continuation (Catto intake)

The submitted `u=U`, `uStar=-V` does not have its claimed positive cyclic
fusion with the submitted product. Reuse the existing
`Canonical.GunaydinGurseyQuarkBasisBridge` dictionary instead:
`u=V`, `uStar=neg U`, `uZero=E22`, `uStarZero=E11`.
`Canonical.PauliWeylTwistorQuarkColorBridge` already proves its six cyclic
fusion identities, square-zero identities, and same/different-color CAR.
No replacement basis or multiplication is needed.

The small continuation is the two explicitly parenthesized triple products,
their associator, and the cyclic nested commutator in this existing dictionary.
The targets are `-uStarZero`, `-uZero`, `uZero-uStarZero`, and
`(-6 : R) • (uZero-uStarZero)`, respectively. The native lower Jacobiator
theorem supplies the last computation. Nonvanishing needs `(6 : R) ≠ 0`;
over characteristic 2 or 3 the Jacobiator shown here vanishes.

The paper's equation/page attribution is not yet checked against its full text.
The abstract complementary-idempotent formula alone does not specify dimensions
6 and 21, a supertrace condition, or an SU(6|21) representation. No such
classification is claimed by this continuation.

Parent verification: the locked `InfoGeometry.Canonical.GunaydinGurseyTripleProductsAudit`
build passed (3100 jobs). Its eight axiom reports have union exactly
`propext`, `Classical.choice`, `Quot.sound`. Independent semantic review passed
for both owners. Independent QA reran the locked audit successfully (3100 jobs,
two package warnings and zero owner/dependency-source warnings) and accepted
the eight-identity scope. Strict source screening reported zero traps.

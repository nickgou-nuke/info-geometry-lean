# Native Zorn Majorana and color contract

The intake proposes duplicate coordinate carriers and a gl(3|1) classification.
This integration uses `InfoGeometry.Algebra.ZornVectorMatrix R`, `L_map`, and
`Module.End R (ZornVectorMatrix R)` over `CommRing R`.

## Ground truth and conventions

`InfoGeometry.Algebra.ZornVectorMatrix.left_E11_apply` sends `(a,v,w,b)` to `(a,v,0,0)`.
`left_diagonal_difference_apply` sends it to `(a,v,-w,-b)`.
`left_E11_tangent_offDiagonal` proves `P L + L P = L` for every
left off-diagonal action. `InfoGeometry.Algebra.ZornVectorMatrix.left_three_mode_product` identifies
the three signed mode commutators with that same grading.
These staged owner files are reused without modification.

Write Q_i = L(U_i), C_i = L(-V_i). The signed mixed CAR is negative.
Mplus = Q-C and Mminus = Q+C have squares +1 and -1 respectively.
The mode commutator [C,Q] = Mminus Mplus; its product over the three modes
is L(diagonal 1 (-1)). The proposed projection `(0,v,0,b)` is replaced by
L(E11): Q_i sends the b coordinate into the upper vector, so retaining both
cannot give its tangent equation.

## Integration scope

Review the existing sandbox candidates for signed CAR, color bilinears and
vector-parametric Majoranas before promoting them. Generic negative-CAR
bilinear actions and commutators reuse
`OperatorAlgebra.QuadraticNoncommutativeIdentity`.
`InfoGeometry.Canonical.GunaydinGursey.car_relations` uses V,-U, so the signed
operator consequences explicitly translate to U,-V via alternativity.
The real-specialized `ZornLeftCAR` already supplies a Clifford representation;
no replacement representation or duplicate octonion carrier is introduced.

Add small reusable operator identities for Majorana parity, collective squares,
and rotation covariance. All candidates require locked compilation, axiom
inspection and independent semantic/acceptance review.

## Scope boundaries

Central odd CAR brackets plus gl(3) bilinears are not a gl(3|1) classification.
Signed dual is not an asserted Hilbert adjoint. An algebraic tangent equation
is not a construction of a super-Grassmannian functor. Over characteristic two
anticommutation does not recover tangency by cancellation; tangency is proved
directly. No nonzero scalar-charge assertion is made in arbitrary characteristic.

## Verification — 2026-10-24

Integrated modules: `Algebra.ZornSignedCAR`, `Algebra.ZornColorBilinears`,
`Algebra.ZornLeftMajorana`, and `Algebra.ZornMajoranaRotations`.
`Algebra.ZornMajoranaColorAudit` imports the integration and audits all 40
named theorem declarations. The final independent locked build of that target
completed successfully (8940 jobs), with zero warnings in these new modules.
The transitive axiom union is `propext`, `Classical.choice`, `Quot.sound`.
Strict screening found zero traps. Independent semantic review and acceptance
both passed for this scope. The final QA log is
`/tmp/zorn-majorana-color-final-qa.log` (session-local evidence).

The implementation reuses the pre-existing staged grading/parity owners and
the staged generic negative-CAR actions. It does not certify unrelated staged
sources or the entire repository. No dependency pins or existing owners were
modified by this integration.

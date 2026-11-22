# Peirce derivation connection: ground-truth contract

Date: 2026-11-22. Intake: [GRADED_NULL_OPERATOR_INTAKE.md](GRADED_NULL_OPERATOR_INTAKE.md).
Base: `fe24e350b08fdea04f74c0748ef9fd9417c47529`.
This contract was written before the new Lean owner. Compilation and independent
acceptance results belong in the focused verification report.

## Claim ledger

| Intake claim | Exact algebraic content and hypotheses | Source-grounded disposition |
| --- | --- | --- |
| Complementary null halves | A symmetric nondegenerate pairing restricts to zero on both complementary subspaces. For a nonzero real underlying space, the doubled model's form is indefinite. | Existing `RealDoubledChiralKrein` and complements owners. Nullity for this form does not imply zero positive norm, mass, or energy. A totally isotropic subspace is not the whole nullcone. |
| Grading and swapping mirror | `Gamma^2 = J^2 = 1` and `Gamma*J = -J*Gamma`; the derived real phase `I = J*Gamma` squares to `-1`. | Existing `Krein/DoubledSpace`: `complex_i_sq` and `modular_j_spectral_epsilon_anticommute`. Mere inequality `Gamma != J` is too weak; no complex scalar is introduced. |
| Peirce bridges | For `q=1-p`, `X=q*a*p`, `Y=p*b*q`: `X^2=Y^2=0`, `F^2=X*Y+Y*X`, `[Y,X]=(p-q)*F^2`. | Existing `PeirceSpine.Tetraktys` and quadratic-cycle owners. Source `conePlus` is the upper bridge `Y`; reversing its assignment reverses the commutator sign. |
| Positive square/metric | With a positive inner product and `Y = adjoint X`, `F^2` is positive semidefinite. Without this, `X=e21`, `Y=-e12` gives `F^2=-1`. | Conditional positivity; no general positivity follows from nilpotence. A compatible fundamental symmetry gives the positive form `B(v,J*w)`. |
| Diagonal idempotency defect | If the full block operator is idempotent, its diagonal block equations identify `Y*X=T-T^2` and `X*Y=G-G^2`. | Requires idempotency of the full operator. Not true for an arbitrary endomorphism. |
| Mirror normalization | If `F` itself is an involutive mirror then `F^2=1`. | A nonzero `1-F^2` is then impossible. Arbitrary odd bridge operators need not be mirrors. |
| Ordinary logarithmic derivative | For degree-zero Leibniz `D`, `D(g^-1*Dg)+(g^-1*Dg)^2=g^-1*D^2g`. | Distinct from an exterior curvature equation. Existing `PeirceMaurerCartanCurvatureWitness` legitimately has nonzero single-derivation examples. |
| Exterior Maurer–Cartan form | For the existing Lie-action exterior calculus, `theta_x=g^-1*rho_x(g)` is flat, including the `-theta_[x,y]` term. | Existing `MaurerCartanTower.actionThetaL_flat`, without faithfulness. Nonzero pure-gauge exterior curvature is an overclaim. |
| Projected curvature from off-diagonal motion | On `pA`, `nabla_x(s)=p*rho_x(s)` has curvature `p*[rho_x(p),rho_y(p)]*p`, acting on sections. | **Missing generic bridge selected here.** Existing `PeirceProjectedConnection` proves only the inner action `rho_a=[a,-]`. |
| Clifford tower | Native real graded tensor equivalences and actual direct-limit parity/differentials. | Existing `Cl11GradedTensorMorita`, `Cl11GradedTensorUntwist`, `Cl11GradedDifferential`, `SplitCliffordSuperGradeColimit`; no duplicate matrix tower. The pair `(Gamma,J)` has squares `(+1,+1)`; `(J,J*Gamma)` has `(+1,-1)`. |
| Octonions and split G2 | A nonassociative product and its product-preserving automorphisms require additional data. | Associative Clifford matrices do not become octonions by increasing size. A representation/associator or triality bridge must be explicit. |
| KMS/QFT/physical and number-theoretic identifications | Need represented algebras, state/dynamics, analytic conditions, appropriate limits, and explicit comparison maps. | Not consequences of this theorem. Existing domain owners must be checked with their own hypotheses. |

## Owner search and reuse

The independent source audit searched canonical `lean/InfoGeometry` and parallel
`src/InfoGeometry`, alternate projected/Grassmann/derivation names, direct
`projectorCurvature` consumers, and relevant imports and theorem bodies.
`Canonical/ProjectedConnectionTransport` transports a linear shadow and is not
the proposed general connection. No arbitrary-`LieActionLane` Grassmann
connection was found in that bounded search.

The implementation imports only:

```lean
import InfoGeometry.OperatorAlgebra.PeirceProjectedConnection
import InfoGeometry.OperatorAlgebra.DerivationExteriorCalculus
```

Reused declarations:

- `Algebra.LieActionLane.operatorAction` and
  `operatorAction_commutator_apply`: actual representation by native `Module.End`.
- `DerivationDifferentialForms.IsLeibnizAction`: the existing noncommutative
  Leibniz predicate; multiplication of coefficients remains noncommutative.
- `PeirceProjectedConnection.peirceRange`, `rangeProjection`,
  `rightMultiplication`, `leftCornerAction`, and `projectedConnection`.
- `Core.PeirceTangent.tangent_iff_diagonal_corners_zero`.
- `ChiralProjectorBerryCurvature.projectorCurvature` and
  `PeirceCompressionCurvature.projectorCurvature_left`,
  `compressedGram_sub_swap_eq_projectorCurvature`.
- Existing `innerLieActionLane : LieActionLane ℤ A` for compatibility with the
  old inner connection over integer scalars. The generic connection retains
  arbitrary commutative scalars; the heavier `MaurerCartanTower` is not imported.

No new differential algebra, null-space carrier, curvature coefficient,
projection carrier, or theorem-bearing structure is introduced. Mathlib's
ordinary `Derivation` interface assumes a commutative coefficient algebra and
is not substituted for the existing noncommutative derivation owner.

## Exact formal intent

Carrier and scalar assumptions:

```lean
{R A : Type*} [CommRing R] [Ring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]
(K : LieActionLane R A) (hK : IsLeibnizAction K)
(p : A) (hp : p * p = p)
```

The scalar hypotheses are exactly those used by the existing linear Peirce
operators; an `Algebra R A` instance supplies them. No faithful action,
stationarity of `p`, star operation, positivity, finite dimension, division by
two, or commutativity of `A` is assumed. Multiplication in `Module.End` means
composition, with the right factor applied first; `[x,y]` is the given Lie
bracket and the coefficient commutator is `x*y-y*x`.

Define a native linear map in the direction variable:

```lean
derivationConnection K p hp : K.L →ₗ[R] Module.End R (peirceRange (R := R) p)
```

At direction `x`, its endomorphism is the composition
`rangeProjection p hp ∘ K.operatorAction x ∘ (peirceRange p).subtype`.
For a section `s`, its value in `A` is `p * K.operatorAction x s`.

The main operator equality is:

```lean
derivationConnection K p hp x * derivationConnection K p hp y -
    derivationConnection K p hp y * derivationConnection K p hp x -
    derivationConnection K p hp ⁅x, y⁆ =
  leftCornerAction p
    (projectorCurvature p (K.operatorAction x p) (K.operatorAction y p))
    (projectorCurvature_left hp (K.operatorAction x p) (K.operatorAction y p))
```

Required companions: derivative tangency; raw section curvature identity;
right-module Leibniz identity as an equality of native endomorphisms;
alternating compressed-Gram readout; flatness when all directions fix `p`;
and compatibility with the existing inner projected connection. The generic
theorem must not assume its desired curvature conclusion.

## Causal proof order

1. The Leibniz rule differentiates `p*p=p` into
   `p*rho_x(p)+rho_x(p)*p=rho_x(p)`.
2. Existing Peirce tangency gives `p*rho_x(p)*p=0`.
3. The Lie-action law cancels the ambient curvature, including its bracket term.
4. Differentiating `p*s=s` rewrites the residual terms as the two ordered
   cross-sector excursions, yielding the raw curvature identity.
5. Native submodule/endomorphism extensionality gives the operator theorem;
   the existing compressed-Gram theorem gives its corner readout.
6. The inner specialization identifies the new operator with the old owner.

These are proof dependencies. The physical, positivity, octonionic, analytic,
and KMS interpretations in the intake are outside this proved dependency chain.

## Verification and acceptance plan

Owner: `lean/InfoGeometry/OperatorAlgebra/PeirceDerivationConnection.lean`.
Expose the owner through `lean/InfoGeometry.lean`; keep the declaration audit
out of that umbrella. Use a focused package with exactly the root Lean and
Mathlib pins and the maintained shared lock. The restored root workspace still
has unavailable external path dependencies, so focused success cannot certify
the whole repository.

Generation, independent semantic audit, and acceptance QA are separate roles.
Run focused kernel/file and Lake checks, complete public declaration axiom
inspection, placeholder screening, semantic-vacuity and staged-proof gates.
Record exact commands, source hashes, inherited warnings, and any blocked gates.
Permitted foundational axioms are only `propext`, `Classical.choice`, `Quot.sound`.

Mathematical reference: Alain Connes, *C* algebras and Differential Geometry*,
1980 note (2001 English translation), Definitions 2–3 and the Grassmann
connection formula, <https://arxiv.org/abs/hep-th/0101093>. This implementation
proves the algebraic Lie-action identity; it does not assume the analytic
C*-dynamical setting used for the reference's further results.

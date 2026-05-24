import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.SouriauThermodynamics

/-!
# InfoGeometry.Canonical.SouriauCasimirInvariant

Affine dual-flat operator algebra symmetry:
geometry as invariants of the affine coadjoint action.

This file defines the abstract affine-coadjoint/Casimir surface for Souriau
thermodynamics.

Boundary with `SouriauThermodynamics`:

* `SouriauThermodynamics.lean` owns finite-dimensional Gibbs/Massieu/Fisher
  response data and finite entropy-production readouts.
* This file is the abstract invariant-theory target (affine/coadjoint
  symmetry, generalized Casimir equation, Legendre/Massieu readout), without
  claiming a full concrete coadjoint-orbit model.

This file does not assert a trajectory-level entropy-production statement
`dS/dt = 0`. It only records affine-coadjoint invariance
`S (Ad#_g Q) = S(Q)`. Orbit-dynamics derivatives belong in a later owner file.

It does not instantiate `G₂(2)`, `G2*`, `Spin(5,5)`, split octonions, or
twistors as completed coadjoint-orbit models. Those require separate
group-specific Ad/Ad*, cocycle, orbit, and moment-map proofs.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauCasimirInvariant

/--
Affine coadjoint data.

This is the Souriau non-equivariant moment-map setting:

`Ad#_g Q = coAd g Q + theta g`.

The cocycle law is kept as data because it is exactly what must be proved for
each concrete Lie group.
-/
structure AffineCoadjointDatum
    (𝕜 G Lie LieDual : Type*)
    [Field 𝕜] [Group G]
    [AddCommGroup Lie] [Module 𝕜 Lie]
    [AddCommGroup LieDual] [Module 𝕜 LieDual] where

  /-- Adjoint representation. -/
  Ad : G → Lie →ₗ[𝕜] Lie

  /-- Coadjoint representation. -/
  coAd : G → LieDual →ₗ[𝕜] LieDual

  /-- Souriau affine one-cocycle. -/
  theta : G → LieDual

  /-- `Ad_1 = id`. -/
  Ad_one :
    Ad 1 = LinearMap.id

  /-- `Ad_{gh} = Ad_g ∘ Ad_h`. -/
  Ad_mul :
    ∀ g h : G,
      Ad (g * h) = (Ad g).comp (Ad h)

  /-- `coAd_1 = id`. -/
  coAd_one :
    coAd 1 = LinearMap.id

  /-- `coAd_{gh} = coAd_g ∘ coAd_h`. -/
  coAd_mul :
    ∀ g h : G,
      coAd (g * h) = (coAd g).comp (coAd h)

  /-- The Souriau one-cocycle vanishes at the identity. -/
  theta_one :
    theta 1 = 0

  /--
  Souriau affine cocycle law:

  `θ(gh) = θ(g) + coAd_g θ(h)`.
  -/
  theta_mul :
    ∀ g h : G,
      theta (g * h) = theta g + coAd g (theta h)

namespace AffineCoadjointDatum

variable {𝕜 G Lie LieDual : Type*}
variable [Field 𝕜] [Group G]
variable [AddCommGroup Lie] [Module 𝕜 Lie]
variable [AddCommGroup LieDual] [Module 𝕜 LieDual]

/-- Affine coadjoint action `Ad#`. -/
def affineCoAd
    (D : AffineCoadjointDatum 𝕜 G Lie LieDual)
    (g : G) (Q : LieDual) : LieDual :=
  D.coAd g Q + D.theta g

/-- The affine coadjoint action fixes identity. -/
@[simp] theorem affineCoAd_one
    (D : AffineCoadjointDatum 𝕜 G Lie LieDual)
    (Q : LieDual) :
    D.affineCoAd 1 Q = Q := by
  unfold affineCoAd
  rw [D.coAd_one, D.theta_one]
  simp

/-- The affine coadjoint action is a genuine action. -/
theorem affineCoAd_mul
    (D : AffineCoadjointDatum 𝕜 G Lie LieDual)
    (g h : G) (Q : LieDual) :
    D.affineCoAd (g * h) Q =
      D.affineCoAd g (D.affineCoAd h Q) := by
  unfold affineCoAd
  rw [D.coAd_mul, D.theta_mul]
  simp [LinearMap.comp_apply, map_add, add_left_comm, add_comm]

end AffineCoadjointDatum


/--
Souriau generalized Casimir entropy datum.

This records the invariant entropy function and its infinitesimal Casimir
equation in the affine-coadjoint setting.

The fields are not fake proofs: each one is a concrete theorem obligation for
a future group-specific model.
-/
structure SouriauCasimirEntropyDatum
    (𝕜 G Lie LieDual : Type*)
    [Field 𝕜] [Group G]
    [AddCommGroup Lie] [Module 𝕜 Lie]
    [AddCommGroup LieDual] [Module 𝕜 LieDual] where

  /-- Affine coadjoint structure. -/
  affine :
    AffineCoadjointDatum 𝕜 G Lie LieDual

  /-- Dual pairing between heat `Q ∈ g*` and temperature `β ∈ g`. -/
  pair : LieDual → Lie → 𝕜

  /-- Souriau entropy on the dual Lie algebra. -/
  entropy : LieDual → 𝕜

  /-- Massieu/log-partition potential on the Lie algebra. -/
  massieu : Lie → 𝕜

  /-- Legendre-dual temperature map `β = ∂S/∂Q`, abstracted. -/
  betaOfHeat : LieDual → Lie

  /-- Infinitesimal coadjoint action. -/
  coadInf : Lie → LieDual →ₗ[𝕜] LieDual

  /--
  Infinitesimal Souriau cocycle `Θ`.

  Pairing this with another Lie algebra element gives the usual two-cocycle:
  `Θe X Y = <Theta X, Y>`.
  -/
  Theta : Lie → LieDual

  /--
  Legendre/Fenchel readout:

  `S(Q) = <Q, β(Q)> - Φ(β(Q))`.
  -/
  entropy_legendre :
    ∀ Q : LieDual,
      entropy Q =
        pair Q (betaOfHeat Q) - massieu (betaOfHeat Q)

  /--
  Entropy is invariant under the affine coadjoint action:

  `S(Ad#_g Q) = S(Q)`.
  -/
  entropy_affineCoAd_invariant :
    ∀ g : G, ∀ Q : LieDual,
      entropy (affine.affineCoAd g Q) = entropy Q

  /--
  Souriau generalized Casimir equation:

  `ad*_{∂S/∂Q} Q + Θ(∂S/∂Q) = 0`.
  -/
  entropy_generalizedCasimir_equation :
    ∀ Q : LieDual,
      coadInf (betaOfHeat Q) Q + Theta (betaOfHeat Q) = 0

namespace SouriauCasimirEntropyDatum

variable {𝕜 G Lie LieDual : Type*}
variable [Field 𝕜] [Group G]
variable [AddCommGroup Lie] [Module 𝕜 Lie]
variable [AddCommGroup LieDual] [Module 𝕜 LieDual]

/--
The affine Lie-Poisson vector field with cocycle:

`ad*_β Q + Θ(β)`.
-/
def affineLiePoissonVector
    (D : SouriauCasimirEntropyDatum 𝕜 G Lie LieDual)
    (β : Lie) (Q : LieDual) : LieDual :=
  D.coadInf β Q + D.Theta β

/--
A scalar on the coadjoint side is geometric when it is invariant under the
affine coadjoint action.
-/
def GeometryInvariant
    (D : SouriauCasimirEntropyDatum 𝕜 G Lie LieDual)
    (F : LieDual → 𝕜) : Prop :=
  ∀ g : G, ∀ Q : LieDual,
    F (D.affine.affineCoAd g Q) = F Q

/--
Souriau/Fenchel defect on the affine-coadjoint side.

This is the affine-coadjoint analogue of the scalar Fenchel/Bregman defect:
`⟪Q,β(Q)⟫ - Φ(β(Q)) - S(Q)`.
-/
def fenchelDefect
    (D : SouriauCasimirEntropyDatum 𝕜 G Lie LieDual)
    (Q : LieDual) : 𝕜 :=
  D.pair Q (D.betaOfHeat Q) - D.massieu (D.betaOfHeat Q) - D.entropy Q

/-- Readout form of the geometry-invariant definition. -/
theorem geometryInvariant_iff
    (D : SouriauCasimirEntropyDatum 𝕜 G Lie LieDual)
    (F : LieDual → 𝕜) :
    D.GeometryInvariant F ↔
      (∀ g : G, ∀ Q : LieDual,
        F (D.affine.affineCoAd g Q) = F Q) :=
  Iff.rfl

/-- Readout: entropy is an affine-coadjoint invariant. -/
theorem entropy_is_affine_coadjoint_invariant
    (D : SouriauCasimirEntropyDatum 𝕜 G Lie LieDual)
    (g : G) (Q : LieDual) :
    D.entropy (D.affine.affineCoAd g Q) =
      D.entropy Q :=
  D.entropy_affineCoAd_invariant g Q

/-- The entropy is a geometry invariant in the Erlangen Operator sense. -/
theorem entropy_geometryInvariant
    (D : SouriauCasimirEntropyDatum 𝕜 G Lie LieDual) :
    D.GeometryInvariant D.entropy := by
  intro g Q
  exact D.entropy_affineCoAd_invariant g Q

/-- Readout: entropy satisfies the generalized Casimir equation. -/
theorem entropy_is_generalized_casimir
    (D : SouriauCasimirEntropyDatum 𝕜 G Lie LieDual)
    (Q : LieDual) :
    D.affineLiePoissonVector (D.betaOfHeat Q) Q = 0 :=
  D.entropy_generalizedCasimir_equation Q

/-- Readout: affine coadjoint identity action fixes every heat vector. -/
@[simp] theorem affineCoAd_one_apply
    (D : SouriauCasimirEntropyDatum 𝕜 G Lie LieDual)
    (Q : LieDual) :
    D.affine.affineCoAd 1 Q = Q :=
  AffineCoadjointDatum.affineCoAd_one D.affine Q

/-- Readout: affine coadjoint action composes by group multiplication. -/
theorem affineCoAd_mul_apply
    (D : SouriauCasimirEntropyDatum 𝕜 G Lie LieDual)
    (g h : G) (Q : LieDual) :
    D.affine.affineCoAd (g * h) Q =
      D.affine.affineCoAd g (D.affine.affineCoAd h Q) :=
  AffineCoadjointDatum.affineCoAd_mul D.affine g h Q

/-- Legendre/Fenchel readout for entropy and Massieu potential. -/
theorem entropy_eq_pair_beta_minus_massieu
    (D : SouriauCasimirEntropyDatum 𝕜 G Lie LieDual)
    (Q : LieDual) :
    D.entropy Q =
      D.pair Q (D.betaOfHeat Q) - D.massieu (D.betaOfHeat Q) :=
  D.entropy_legendre Q

/-- Legendre contact identity: the Souriau/Fenchel defect vanishes. -/
theorem fenchelDefect_eq_zero
    (D : SouriauCasimirEntropyDatum 𝕜 G Lie LieDual)
    (Q : LieDual) :
    D.fenchelDefect Q = 0 := by
  unfold fenchelDefect
  rw [D.entropy_eq_pair_beta_minus_massieu Q]
  ring

/--
Affine-coadjoint invariance of the Souriau/Fenchel defect under symmetry laws
for pairing, Massieu potential, and dual-coordinate transport.
-/
theorem fenchelDefect_affineCoAd_invariant_of_preserves_pair_massieu_beta
    (D : SouriauCasimirEntropyDatum 𝕜 G Lie LieDual)
    (hPair :
      ∀ g : G, ∀ Q : LieDual, ∀ β : Lie,
        D.pair (D.affine.affineCoAd g Q) (D.affine.Ad g β) = D.pair Q β)
    (hMassieu :
      ∀ g : G, ∀ β : Lie,
        D.massieu (D.affine.Ad g β) = D.massieu β)
    (hBeta :
      ∀ g : G, ∀ Q : LieDual,
        D.betaOfHeat (D.affine.affineCoAd g Q) = D.affine.Ad g (D.betaOfHeat Q))
    (g : G) (Q : LieDual) :
    D.fenchelDefect (D.affine.affineCoAd g Q) = D.fenchelDefect Q := by
  unfold fenchelDefect
  rw [hBeta g Q]
  rw [hPair g Q (D.betaOfHeat Q)]
  rw [hMassieu g (D.betaOfHeat Q)]
  rw [D.entropy_affineCoAd_invariant g Q]

end SouriauCasimirEntropyDatum

/-! ## Operatorial Fenchel-Legendre lift along affine coadjoint orbits -/

/--
Operatorial Fenchel defect.

This is the Lie-side analogue of the scalar Fenchel gap

`ψ(θ) + φ(η) - θη`.

Here:

* `massieu ξ` is the adjoint-side Massieu/log-partition potential;
* `entropy Q` is the coadjoint-side entropy;
* `pair Q ξ` is the Lie pairing `<Q, ξ>`.
-/
def operatorFenchelGap
    {𝕜 Lie LieDual : Type*} [Sub 𝕜] [Add 𝕜]
    (pair : LieDual → Lie → 𝕜)
    (massieu : Lie → 𝕜)
    (entropy : LieDual → 𝕜)
    (Q : LieDual) (ξ : Lie) : 𝕜 :=
  massieu ξ + entropy Q - pair Q ξ

/--
Real operatorial Legendre-Fenchel lemma.

The Fenchel defect is invariant under simultaneous adjoint and affine
coadjoint transport, provided:

* the pairing is additive in the coadjoint argument;
* the ordinary coadjoint/adjoint pairing is invariant;
* the Massieu potential transforms by the Souriau affine cocycle;
* entropy is affine-coadjoint invariant.

Mathematically, with

`Ad#_g Q = coAd_g Q + θ(g)`,

this proves

`Gap(Ad#_g Q, Ad_g ξ) = Gap(Q, ξ)`.
-/
theorem operatorFenchelGap_affineCoAd_invariant
    {𝕜 G Lie LieDual : Type*}
    [AddCommGroup 𝕜] [Group G] [AddCommGroup LieDual]
    (Ad : G → Lie → Lie)
    (coAd : G → LieDual → LieDual)
    (theta : G → LieDual)
    (pair : LieDual → Lie → 𝕜)
    (massieu : Lie → 𝕜)
    (entropy : LieDual → 𝕜)
    (hpair_add :
      ∀ Q R ξ,
        pair (Q + R) ξ = pair Q ξ + pair R ξ)
    (hpair_coAd_Ad :
      ∀ g Q ξ,
        pair (coAd g Q) (Ad g ξ) = pair Q ξ)
    (hmassieu_affine :
      ∀ g ξ,
        massieu (Ad g ξ) =
          massieu ξ + pair (theta g) (Ad g ξ))
    (hentropy_affine :
      ∀ g Q,
        entropy (coAd g Q + theta g) = entropy Q)
    (g : G) (Q : LieDual) (ξ : Lie) :
    operatorFenchelGap pair massieu entropy
        (coAd g Q + theta g) (Ad g ξ)
      =
    operatorFenchelGap pair massieu entropy Q ξ := by
  unfold operatorFenchelGap
  rw [hmassieu_affine g ξ]
  rw [hentropy_affine g Q]
  rw [hpair_add (coAd g Q) (theta g) (Ad g ξ)]
  rw [hpair_coAd_Ad g Q ξ]
  abel

/--
Entropy invariance from the operatorial Legendre-Fenchel readout.

Assume entropy is represented by the generalized Legendre transform

`S(Q) = <Q, β(Q)> - Φ(β(Q))`.

If the dual coordinate is equivariant,

`β(Ad#_g Q) = Ad_g β(Q)`,

and the pairing/Massieu terms transform by the affine Souriau rules, then
entropy is constant along the affine coadjoint orbit.
-/
theorem operatorLegendre_entropy_affineCoAd_invariant
    {𝕜 G Lie LieDual : Type*}
    [AddCommGroup 𝕜] [Group G] [AddCommGroup LieDual]
    (Ad : G → Lie → Lie)
    (coAd : G → LieDual → LieDual)
    (theta : G → LieDual)
    (pair : LieDual → Lie → 𝕜)
    (massieu : Lie → 𝕜)
    (entropy : LieDual → 𝕜)
    (beta : LieDual → Lie)
    (hentropy_legendre :
      ∀ Q,
        entropy Q = pair Q (beta Q) - massieu (beta Q))
    (hbeta_affine :
      ∀ g Q,
        beta (coAd g Q + theta g) = Ad g (beta Q))
    (hpair_add :
      ∀ Q R ξ,
        pair (Q + R) ξ = pair Q ξ + pair R ξ)
    (hpair_coAd_Ad :
      ∀ g Q ξ,
        pair (coAd g Q) (Ad g ξ) = pair Q ξ)
    (hmassieu_affine :
      ∀ g ξ,
        massieu (Ad g ξ) =
          massieu ξ + pair (theta g) (Ad g ξ))
    (g : G) (Q : LieDual) :
    entropy (coAd g Q + theta g) = entropy Q := by
  rw [hentropy_legendre (coAd g Q + theta g)]
  rw [hentropy_legendre Q]
  rw [hbeta_affine g Q]
  rw [hpair_add (coAd g Q) (theta g) (Ad g (beta Q))]
  rw [hpair_coAd_Ad g Q (beta Q)]
  rw [hmassieu_affine g (beta Q)]
  abel

/--
Operatorial Legendre/Fenchel covariance implies affine-coadjoint entropy
invariance.

This is the operator-lifted Souriau readout:
`EntropyOp ρ = <ρ, β(ρ)> - MassieuOp (β(ρ))`.
-/
theorem operator_entropy_affine_invariant_of_legendre_covariant
    {𝕜 G StateOp TempOp : Type*} [Sub 𝕜]
    (EntropyOp : StateOp → 𝕜)
    (MassieuOp : TempOp → 𝕜)
    (pairOp : StateOp → TempOp → 𝕜)
    (betaOfState : StateOp → TempOp)
    (AdSharp : G → StateOp → StateOp)
    (AdTemp : G → TempOp → TempOp)
    (g : G) (ρ : StateOp)
    (hLegendre :
      ∀ ρ : StateOp,
        EntropyOp ρ =
          pairOp ρ (betaOfState ρ) - MassieuOp (betaOfState ρ))
    (hBeta :
      betaOfState (AdSharp g ρ) = AdTemp g (betaOfState ρ))
    (hPair :
      pairOp (AdSharp g ρ) (AdTemp g (betaOfState ρ)) =
        pairOp ρ (betaOfState ρ))
    (hMassieu :
      MassieuOp (AdTemp g (betaOfState ρ)) =
        MassieuOp (betaOfState ρ)) :
    EntropyOp (AdSharp g ρ) = EntropyOp ρ := by
  rw [hLegendre (AdSharp g ρ)]
  rw [hBeta]
  rw [hPair]
  rw [hMassieu]
  rw [hLegendre ρ]

/--
Operatorial Bregman/Fenchel divergence is invariant under the affine-coadjoint
operator action.
-/
theorem operator_bregman_affine_invariant
    {𝕜 G StateOp TempOp : Type*} [Sub 𝕜]
    (EntropyOp : StateOp → 𝕜)
    (pairDiffOp : StateOp → StateOp → TempOp → 𝕜)
    (betaOfState : StateOp → TempOp)
    (AdSharp : G → StateOp → StateOp)
    (AdTemp : G → TempOp → TempOp)
    (g : G) (ρ₁ ρ₂ : StateOp)
    (hEntropy :
      ∀ ρ : StateOp,
        EntropyOp (AdSharp g ρ) = EntropyOp ρ)
    (hBeta :
      betaOfState (AdSharp g ρ₂) = AdTemp g (betaOfState ρ₂))
    (hPairDiff :
      pairDiffOp
          (AdSharp g ρ₁)
          (AdSharp g ρ₂)
          (AdTemp g (betaOfState ρ₂))
        =
      pairDiffOp ρ₁ ρ₂ (betaOfState ρ₂)) :
    EntropyOp (AdSharp g ρ₁)
      - EntropyOp (AdSharp g ρ₂)
      - pairDiffOp
          (AdSharp g ρ₁)
          (AdSharp g ρ₂)
          (betaOfState (AdSharp g ρ₂))
    =
    EntropyOp ρ₁
      - EntropyOp ρ₂
      - pairDiffOp ρ₁ ρ₂ (betaOfState ρ₂) := by
  rw [hEntropy ρ₁]
  rw [hEntropy ρ₂]
  rw [hBeta]
  rw [hPairDiff]


/--
Refinement for the zero-cohomology case.

This is the specialization where the affine cocycle vanishes globally,
so the affine coadjoint action reduces to the ordinary coadjoint action.
-/
structure SouriauZeroCohomologyDatum
    (𝕜 G Lie LieDual : Type*)
    [Field 𝕜] [Group G]
    [AddCommGroup Lie] [Module 𝕜 Lie]
    [AddCommGroup LieDual] [Module 𝕜 LieDual] where

  /-- Underlying Souriau Casimir entropy datum. -/
  base :
    SouriauCasimirEntropyDatum 𝕜 G Lie LieDual

  /-- Vanishing affine cocycle. -/
  theta_zero :
    ∀ g : G, base.affine.theta g = 0

namespace SouriauZeroCohomologyDatum

variable {𝕜 G Lie LieDual : Type*}
variable [Field 𝕜] [Group G]
variable [AddCommGroup Lie] [Module 𝕜 Lie]
variable [AddCommGroup LieDual] [Module 𝕜 LieDual]

/-- In the zero-cohomology case, affine coadjoint equals ordinary coadjoint. -/
theorem affineCoAd_eq_coAd
    (D : SouriauZeroCohomologyDatum 𝕜 G Lie LieDual)
    (g : G) (Q : LieDual) :
    D.base.affine.affineCoAd g Q = D.base.affine.coAd g Q := by
  unfold AffineCoadjointDatum.affineCoAd
  rw [D.theta_zero g]
  simp

/-- Entropy invariance remains valid in the zero-cohomology specialization. -/
theorem entropy_geometryInvariant
    (D : SouriauZeroCohomologyDatum 𝕜 G Lie LieDual) :
    D.base.GeometryInvariant D.base.entropy :=
  D.base.entropy_geometryInvariant

/-- Generalized Casimir equation remains valid in the zero-cohomology specialization. -/
theorem entropy_is_generalized_casimir
    (D : SouriauZeroCohomologyDatum 𝕜 G Lie LieDual)
    (Q : LieDual) :
    D.base.affineLiePoissonVector (D.base.betaOfHeat Q) Q = 0 :=
  D.base.entropy_is_generalized_casimir Q

end SouriauZeroCohomologyDatum

/--
Refinement for the nonzero-cohomology case.

The base `SouriauCasimirEntropyDatum` supports both null and non-null
cohomology. This refinement records the explicit theorem-facing obligation
that the infinitesimal cocycle is genuinely nonzero.
-/
structure SouriauNonzeroCohomologyDatum
    (𝕜 G Lie LieDual : Type*)
    [Field 𝕜] [Group G]
    [AddCommGroup Lie] [Module 𝕜 Lie]
    [AddCommGroup LieDual] [Module 𝕜 LieDual] where

  /-- The underlying Souriau Casimir entropy datum. -/
  base :
    SouriauCasimirEntropyDatum 𝕜 G Lie LieDual

  /-- The cocycle is genuinely nonzero. -/
  Theta_nonzero :
    ∃ β : Lie, base.Theta β ≠ 0

namespace SouriauNonzeroCohomologyDatum

variable {𝕜 G Lie LieDual : Type*}
variable [Field 𝕜] [Group G]
variable [AddCommGroup Lie] [Module 𝕜 Lie]
variable [AddCommGroup LieDual] [Module 𝕜 LieDual]

/-- Readout: the model is in the nonzero-cohomology case. -/
theorem nonzero_cohomology
    (D : SouriauNonzeroCohomologyDatum 𝕜 G Lie LieDual) :
    ∃ β : Lie, D.base.Theta β ≠ 0 :=
  D.Theta_nonzero

/-- Even in the nonzero-cohomology case, entropy remains an affine invariant. -/
theorem entropy_geometryInvariant
    (D : SouriauNonzeroCohomologyDatum 𝕜 G Lie LieDual) :
    D.base.GeometryInvariant D.base.entropy :=
  D.base.entropy_geometryInvariant

/-- Even in the nonzero-cohomology case, entropy satisfies the Casimir equation. -/
theorem entropy_is_generalized_casimir
    (D : SouriauNonzeroCohomologyDatum 𝕜 G Lie LieDual)
    (Q : LieDual) :
    D.base.affineLiePoissonVector (D.base.betaOfHeat Q) Q = 0 :=
  D.base.entropy_is_generalized_casimir Q

end SouriauNonzeroCohomologyDatum

end InfoGeometry.Canonical.SouriauCasimirInvariant

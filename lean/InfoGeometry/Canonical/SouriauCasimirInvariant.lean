import Mathlib
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
  symmetry, Casimir equation, Legendre readout), without claiming a full
  concrete coadjoint-orbit model.

This file does not assert a trajectory-level entropy-production statement
`dS/dt = 0`. It only records affine-coadjoint invariance
`S (Ad#_g Q) = S(Q)`. Orbit-dynamics derivatives belong in a later owner file.

It does not instantiate `G₂(2)`, `Spin(5,5)`, split octonions, or twistors.
Those require separate group-specific Ad/Ad*, cocycle, orbit, and moment-map
proofs.
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

/-- Legendre/Fenchel readout for entropy and Massieu potential. -/
theorem entropy_eq_pair_beta_minus_massieu
    (D : SouriauCasimirEntropyDatum 𝕜 G Lie LieDual)
    (Q : LieDual) :
    D.entropy Q =
      D.pair Q (D.betaOfHeat Q) - D.massieu (D.betaOfHeat Q) :=
  D.entropy_legendre Q

end SouriauCasimirEntropyDatum


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

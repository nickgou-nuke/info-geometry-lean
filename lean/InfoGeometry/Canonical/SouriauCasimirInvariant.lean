import Mathlib
import InfoGeometry.Canonical.SouriauThermodynamics

/-!
# InfoGeometry.Canonical.SouriauCasimirInvariant

Erlangen Operator 2.0: geometry as symmetry invariants.

This file defines the abstract affine-coadjoint/Casimir surface for Souriau
thermodynamics.

It does not instantiate `G₂(2)`, `Spin(5,5)`, split octonions, or twistors.
Those require separate group-specific Ad/Ad*, cocycle, orbit, and moment-map
proofs.
-/

noncomputable section

namespace InfoGeometry.Canonical.SouriauCasimirInvariant

/--
Affine coadjoint data.

This is the Souriau non-equivariant moment-map setting:

`Ad#_g Q = coAd g Q + θ g`.

The cocycle law is kept as real data because it is exactly what must be
proved for each concrete Lie group.
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

  /-- Souriau affine cocycle. -/
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
  simp only [LinearMap.comp_apply, map_add]
  abel

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
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    extends AffineCoadjointDatum 𝕜 G Lie LieDual where

  /-- Souriau entropy on the dual Lie algebra. -/
  entropy : LieDual → 𝕜

  /-- Massieu potential on the Lie algebra. -/
  massieu : Lie → 𝕜

  /-- Legendre-dual temperature map `β = ∂S/∂Q`, abstracted. -/
  betaOfHeat : LieDual → Lie

  /-- Infinitesimal coadjoint action. -/
  coadInf : Lie → LieDual →ₗ[𝕜] LieDual

  /-- Infinitesimal cocycle `Θ`. -/
  Theta : Lie → LieDual

  /--
  Entropy is invariant under the affine coadjoint action.

  `S(Ad#_g Q) = S(Q)`.
  -/
  entropy_affineCoAd_invariant :
    ∀ g : G, ∀ Q : LieDual,
      entropy (toAffineCoadjointDatum.affineCoAd g Q) = entropy Q

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

/-- Readout: entropy is an affine-coadjoint invariant. -/
theorem entropy_is_affine_coadjoint_invariant
    (D : SouriauCasimirEntropyDatum 𝕜 G Lie LieDual)
    (g : G) (Q : LieDual) :
    D.entropy (D.toAffineCoadjointDatum.affineCoAd g Q) =
      D.entropy Q :=
  D.entropy_affineCoAd_invariant g Q

/-- Readout: entropy satisfies the generalized Casimir equation. -/
theorem entropy_is_generalized_casimir
    (D : SouriauCasimirEntropyDatum 𝕜 G Lie LieDual)
    (Q : LieDual) :
    D.coadInf (D.betaOfHeat Q) Q + D.Theta (D.betaOfHeat Q) = 0 :=
  D.entropy_generalizedCasimir_equation Q

end SouriauCasimirEntropyDatum

end InfoGeometry.Canonical.SouriauCasimirInvariant

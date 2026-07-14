import Mathlib

/-!
# InfoGeometry.Canonical.SouriauCasimirInvariant

Concrete affine-coadjoint action lemmas.

No structures.
No wrapper datum.
No fake Casimir packet.

This file proves the only algebraic fact needed at this layer:

If `coAd` is a representation and `theta` is a Souriau 1-cocycle,

  θ(gh) = θ(g) + coAd_g θ(h),

then

  Q ↦ coAd_g Q + θ(g)

is a genuine group action.
-/

noncomputable section

namespace SouriauCasimirInvariant

/-- Raw affine coadjoint transport. -/
def affineCoAd
    {𝕜 G LieDual : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    (coAd : G → LieDual →ₗ[𝕜] LieDual)
    (theta : G → LieDual)
    (g : G) (Q : LieDual) : LieDual :=
  coAd g Q + theta g

/--
Identity element acts trivially under affine coadjoint transport.

This uses only:

* `coAd 1 = id`;
* `theta 1 = 0`.
-/
@[simp]
theorem affineCoAd_one
    {𝕜 G LieDual : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    (coAd : G → LieDual →ₗ[𝕜] LieDual)
    (theta : G → LieDual)
    (hcoAd_one : coAd 1 = LinearMap.id)
    (htheta_one : theta 1 = 0)
    (Q : LieDual) :
    affineCoAd coAd theta 1 Q = Q := by
  unfold affineCoAd
  rw [hcoAd_one, htheta_one]
  simp

/--
The Souriau affine coadjoint transport is a genuine action.

Assumptions:

* `coAd (g*h) = coAd g ∘ coAd h`;
* `theta (g*h) = theta g + coAd g (theta h)`.

Conclusion:

`Ad#_(gh) Q = Ad#_g (Ad#_h Q)`.
-/
theorem affineCoAd_mul
    {𝕜 G LieDual : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    (coAd : G → LieDual →ₗ[𝕜] LieDual)
    (theta : G → LieDual)
    (hcoAd_mul :
      ∀ g h : G,
        coAd (g * h) = (coAd g).comp (coAd h))
    (htheta_mul :
      ∀ g h : G,
        theta (g * h) = theta g + coAd g (theta h))
    (g h : G) (Q : LieDual) :
    affineCoAd coAd theta (g * h) Q =
      affineCoAd coAd theta g (affineCoAd coAd theta h Q) := by
  unfold affineCoAd
  rw [hcoAd_mul g h, htheta_mul g h]
  simp only [LinearMap.comp_apply, map_add]
  abel

/--
Left inverse law for the affine coadjoint action.

Applying `g` and then `g⁻¹` returns the original coadjoint point.
This is a genuine consequence of the cocycle law and the group action law.
-/
@[simp]
theorem affineCoAd_inv_mul
    {𝕜 G LieDual : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    (coAd : G → LieDual →ₗ[𝕜] LieDual)
    (theta : G → LieDual)
    (hcoAd_one : coAd 1 = LinearMap.id)
    (hcoAd_mul :
      ∀ g h : G,
        coAd (g * h) = (coAd g).comp (coAd h))
    (htheta_one : theta 1 = 0)
    (htheta_mul :
      ∀ g h : G,
        theta (g * h) = theta g + coAd g (theta h))
    (g : G) (Q : LieDual) :
    affineCoAd coAd theta g⁻¹ (affineCoAd coAd theta g Q) = Q := by
  calc
    affineCoAd coAd theta g⁻¹ (affineCoAd coAd theta g Q)
        = affineCoAd coAd theta (g⁻¹ * g) Q := by
          exact (affineCoAd_mul coAd theta hcoAd_mul htheta_mul g⁻¹ g Q).symm
    _ = affineCoAd coAd theta 1 Q := by
          rw [inv_mul_cancel]
    _ = Q := by
          exact affineCoAd_one coAd theta hcoAd_one htheta_one Q

/--
Right inverse law for the affine coadjoint action.

Applying `g⁻¹` and then `g` returns the original coadjoint point.
-/
@[simp]
theorem affineCoAd_mul_inv
    {𝕜 G LieDual : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    (coAd : G → LieDual →ₗ[𝕜] LieDual)
    (theta : G → LieDual)
    (hcoAd_one : coAd 1 = LinearMap.id)
    (hcoAd_mul :
      ∀ g h : G,
        coAd (g * h) = (coAd g).comp (coAd h))
    (htheta_one : theta 1 = 0)
    (htheta_mul :
      ∀ g h : G,
        theta (g * h) = theta g + coAd g (theta h))
    (g : G) (Q : LieDual) :
    affineCoAd coAd theta g (affineCoAd coAd theta g⁻¹ Q) = Q := by
  calc
    affineCoAd coAd theta g (affineCoAd coAd theta g⁻¹ Q)
        = affineCoAd coAd theta (g * g⁻¹) Q := by
          exact (affineCoAd_mul coAd theta hcoAd_mul htheta_mul g g⁻¹ Q).symm
    _ = affineCoAd coAd theta 1 Q := by
          rw [mul_inv_cancel]
    _ = Q := by
          exact affineCoAd_one coAd theta hcoAd_one htheta_one Q

/--
Cocycle inverse identity:

`θ(g) + coAd_g θ(g⁻¹) = 0`.
-/
theorem theta_mul_inv
    {𝕜 G LieDual : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    (coAd : G → LieDual →ₗ[𝕜] LieDual)
    (theta : G → LieDual)
    (htheta_one : theta 1 = 0)
    (htheta_mul :
      ∀ g h : G,
        theta (g * h) = theta g + coAd g (theta h))
    (g : G) :
    theta g + coAd g (theta g⁻¹) = 0 := by
  have h := htheta_mul g g⁻¹
  simpa [htheta_one] using h.symm

/--
Cocycle inverse identity in the opposite order:

`θ(g⁻¹) + coAd_{g⁻¹} θ(g) = 0`.
-/
theorem theta_inv_mul
    {𝕜 G LieDual : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    (coAd : G → LieDual →ₗ[𝕜] LieDual)
    (theta : G → LieDual)
    (htheta_one : theta 1 = 0)
    (htheta_mul :
      ∀ g h : G,
        theta (g * h) = theta g + coAd g (theta h))
    (g : G) :
    theta g⁻¹ + coAd g⁻¹ (theta g) = 0 := by
  have h := htheta_mul g⁻¹ g
  simpa [htheta_one] using h.symm

/--
The inverse group element gives the left inverse of affine coadjoint transport.
-/
theorem affineCoAd_inv_left
    {𝕜 G LieDual : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    (coAd : G → LieDual →ₗ[𝕜] LieDual)
    (theta : G → LieDual)
    (hcoAd_one : coAd 1 = LinearMap.id)
    (hcoAd_mul :
      ∀ g h : G,
        coAd (g * h) = (coAd g).comp (coAd h))
    (htheta_one : theta 1 = 0)
    (htheta_mul :
      ∀ g h : G,
        theta (g * h) = theta g + coAd g (theta h))
    (g : G) (Q : LieDual) :
    affineCoAd coAd theta g⁻¹ (affineCoAd coAd theta g Q) = Q := by
  calc
    affineCoAd coAd theta g⁻¹ (affineCoAd coAd theta g Q)
        = affineCoAd coAd theta (g⁻¹ * g) Q := by
            exact (affineCoAd_mul coAd theta hcoAd_mul htheta_mul g⁻¹ g Q).symm
    _ = affineCoAd coAd theta 1 Q := by rw [inv_mul_cancel]
    _ = Q := affineCoAd_one coAd theta hcoAd_one htheta_one Q

/--
The inverse group element gives the right inverse of affine coadjoint transport.
-/
theorem affineCoAd_inv_right
    {𝕜 G LieDual : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    (coAd : G → LieDual →ₗ[𝕜] LieDual)
    (theta : G → LieDual)
    (hcoAd_one : coAd 1 = LinearMap.id)
    (hcoAd_mul :
      ∀ g h : G,
        coAd (g * h) = (coAd g).comp (coAd h))
    (htheta_one : theta 1 = 0)
    (htheta_mul :
      ∀ g h : G,
        theta (g * h) = theta g + coAd g (theta h))
    (g : G) (Q : LieDual) :
    affineCoAd coAd theta g (affineCoAd coAd theta g⁻¹ Q) = Q := by
  calc
    affineCoAd coAd theta g (affineCoAd coAd theta g⁻¹ Q)
        = affineCoAd coAd theta (g * g⁻¹) Q := by
            exact (affineCoAd_mul coAd theta hcoAd_mul htheta_mul g g⁻¹ Q).symm
    _ = affineCoAd coAd theta 1 Q := by rw [mul_inv_cancel]
    _ = Q := affineCoAd_one coAd theta hcoAd_one htheta_one Q

/-- Each affine coadjoint transformation is injective. -/
theorem affineCoAd_injective
    {𝕜 G LieDual : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    (coAd : G → LieDual →ₗ[𝕜] LieDual)
    (theta : G → LieDual)
    (hcoAd_one : coAd 1 = LinearMap.id)
    (hcoAd_mul :
      ∀ g h : G,
        coAd (g * h) = (coAd g).comp (coAd h))
    (htheta_one : theta 1 = 0)
    (htheta_mul :
      ∀ g h : G,
        theta (g * h) = theta g + coAd g (theta h))
    (g : G) :
    Function.Injective (affineCoAd coAd theta g) := by
  intro Q₁ Q₂ h
  have h' :
      affineCoAd coAd theta g⁻¹ (affineCoAd coAd theta g Q₁) =
        affineCoAd coAd theta g⁻¹ (affineCoAd coAd theta g Q₂) := by
    rw [h]
  simpa [affineCoAd_inv_left coAd theta hcoAd_one hcoAd_mul htheta_one htheta_mul g] using h'

/-- Each affine coadjoint transformation is surjective. -/
theorem affineCoAd_surjective
    {𝕜 G LieDual : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    (coAd : G → LieDual →ₗ[𝕜] LieDual)
    (theta : G → LieDual)
    (hcoAd_one : coAd 1 = LinearMap.id)
    (hcoAd_mul :
      ∀ g h : G,
        coAd (g * h) = (coAd g).comp (coAd h))
    (htheta_one : theta 1 = 0)
    (htheta_mul :
      ∀ g h : G,
        theta (g * h) = theta g + coAd g (theta h))
    (g : G) :
    Function.Surjective (affineCoAd coAd theta g) := by
  intro Q
  refine ⟨affineCoAd coAd theta g⁻¹ Q, ?_⟩
  exact affineCoAd_inv_right coAd theta hcoAd_one hcoAd_mul htheta_one htheta_mul g Q

/-- Each affine coadjoint transformation is bijective. -/
theorem affineCoAd_bijective
    {𝕜 G LieDual : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    (coAd : G → LieDual →ₗ[𝕜] LieDual)
    (theta : G → LieDual)
    (hcoAd_one : coAd 1 = LinearMap.id)
    (hcoAd_mul :
      ∀ g h : G,
        coAd (g * h) = (coAd g).comp (coAd h))
    (htheta_one : theta 1 = 0)
    (htheta_mul :
      ∀ g h : G,
        theta (g * h) = theta g + coAd g (theta h))
    (g : G) :
    Function.Bijective (affineCoAd coAd theta g) :=
  ⟨affineCoAd_injective coAd theta hcoAd_one hcoAd_mul htheta_one htheta_mul g,
   affineCoAd_surjective coAd theta hcoAd_one hcoAd_mul htheta_one htheta_mul g⟩

/-- Equality is reflected by affine coadjoint transport. -/
theorem affineCoAd_eq_iff
    {𝕜 G LieDual : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    (coAd : G → LieDual →ₗ[𝕜] LieDual)
    (theta : G → LieDual)
    (hcoAd_one : coAd 1 = LinearMap.id)
    (hcoAd_mul :
      ∀ g h : G,
        coAd (g * h) = (coAd g).comp (coAd h))
    (htheta_one : theta 1 = 0)
    (htheta_mul :
      ∀ g h : G,
        theta (g * h) = theta g + coAd g (theta h))
    (g : G) (Q₁ Q₂ : LieDual) :
    affineCoAd coAd theta g Q₁ = affineCoAd coAd theta g Q₂ ↔ Q₁ = Q₂ := by
  constructor
  · intro h
    exact (affineCoAd_injective coAd theta hcoAd_one hcoAd_mul htheta_one htheta_mul g) h
  · intro h
    rw [h]

/--
Affine coadjoint transport acts linearly on differences:

`Ad#_g Q₁ - Ad#_g Q₂ = coAd_g (Q₁ - Q₂)`.
-/
theorem affineCoAd_sub
    {𝕜 G LieDual : Type*}
    [Field 𝕜] [Group G]
    [AddCommGroup LieDual] [Module 𝕜 LieDual]
    (coAd : G → LieDual →ₗ[𝕜] LieDual)
    (theta : G → LieDual)
    (g : G) (Q₁ Q₂ : LieDual) :
    affineCoAd coAd theta g Q₁ - affineCoAd coAd theta g Q₂ =
      coAd g (Q₁ - Q₂) := by
  unfold affineCoAd
  rw [map_sub]
  abel

end SouriauCasimirInvariant

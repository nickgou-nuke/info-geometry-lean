import proofs.ProjectiveUnitary6
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Projective representations and central factor systems

A projective representation is represented by lifts whose multiplication is
correct up to a central factor.  This owner separates the factor system from
its quotient representation and records the normalized cocycle law.
-/

noncomputable section
namespace ProjectiveRepresentation

/-- A normalized central factor system with values in a commutative group. -/
structure NormalizedCocycle (G Z : Type*) [Group G] [CommGroup Z] where
  factor : G → G → Z
  left_one : ∀ g, factor 1 g = 1
  right_one : ∀ g, factor g 1 = 1
  cocycle : ∀ g h k,
    factor g h * factor (g * h) k =
      factor h k * factor g (h * k)

@[simp] theorem NormalizedCocycle.factor_one_left
    {G Z : Type*} [Group G] [CommGroup Z]
    (c : NormalizedCocycle G Z) (g : G) : c.factor 1 g = 1 :=
  c.left_one g

@[simp] theorem NormalizedCocycle.factor_one_right
    {G Z : Type*} [Group G] [CommGroup Z]
    (c : NormalizedCocycle G Z) (g : G) : c.factor g 1 = 1 :=
  c.right_one g

/-- A projective representation with central scalar factor system. -/
structure IsProjectiveRepresentation
    (G U Z : Type*) [Group G] [Group U] [CommGroup Z]
    (ι : Z →* Subgroup.center U) where
  lift : G → U
  factorSystem : NormalizedCocycle G Z
  lift_one : lift 1 = 1
  map_mul : ∀ g h,
    lift g * lift h = (ι (factorSystem.factor g h) : U) * lift (g * h)

namespace IsProjectiveRepresentation

variable {G U Z : Type*} [Group G] [Group U] [CommGroup Z]
variable {ι : Z →* Subgroup.center U}
variable (ρ : IsProjectiveRepresentation G U Z ι)

@[simp] theorem lift_one_eq : ρ.lift 1 = 1 := ρ.lift_one

theorem lift_mul_factor (g h : G) :
    ρ.lift g * ρ.lift h =
      (ι (ρ.factorSystem.factor g h) : U) * ρ.lift (g * h) :=
  ρ.map_mul g h

/-- The central factor disappears in the quotient by the center. -/
def quotientLift : G → (U ⧸ Subgroup.center U) :=
  fun g => QuotientGroup.mk' (Subgroup.center U) (ρ.lift g)

theorem quotientLift_one : quotientLift ρ 1 = 1 := by
  simp [quotientLift, ρ.lift_one]

theorem quotientLift_mul (g h : G) :
    quotientLift ρ (g * h) = quotientLift ρ g * quotientLift ρ h := by
  change QuotientGroup.mk' (Subgroup.center U) (ρ.lift (g * h)) =
    QuotientGroup.mk' (Subgroup.center U) (ρ.lift g) *
      QuotientGroup.mk' (Subgroup.center U) (ρ.lift h)
  rw [ρ.map_mul, map_mul]
  simp

def quotientRepresentation : G →* (U ⧸ Subgroup.center U) where
  toFun := quotientLift ρ
  map_one' := quotientLift_one ρ
  map_mul' := by intro g h; exact quotientLift_mul ρ g h

@[simp] theorem quotientRepresentation_apply (g : G) :
    quotientRepresentation ρ g = quotientLift ρ g := rfl

end IsProjectiveRepresentation

/-- The factor-system multiplication on the central extension carrier. -/
def extensionMul
    {G Z : Type*} [Group G] [CommGroup Z]
    (c : NormalizedCocycle G Z) : (Z × G) → (Z × G) → (Z × G)
  | (z, g), (w, h) => (z * w * c.factor g h, g * h)

theorem extensionMul_assoc
    {G Z : Type*} [Group G] [CommGroup Z]
    (c : NormalizedCocycle G Z) (x y z : Z × G) :
    extensionMul c (extensionMul c x y) z =
      extensionMul c x (extensionMul c y z) := by
  rcases x with ⟨x, g⟩
  rcases y with ⟨y, h⟩
  rcases z with ⟨z, k⟩
  simp only [extensionMul, Prod.mk.injEq]
  constructor
  · calc
      x * (y * (c.factor g h * (z * c.factor (g * h) k))) =
          x * y * z * (c.factor g h * c.factor (g * h) k) := by ac_rfl
      _ = x * y * z * (c.factor h k * c.factor g (h * k)) := by rw [c.cocycle]
      _ = x * (y * (z * (c.factor h k * c.factor g (h * k)))) := by ac_rfl
  · simp [mul_assoc]

theorem extensionMul_one_left
    {G Z : Type*} [Group G] [CommGroup Z]
    (c : NormalizedCocycle G Z) (x : Z × G) :
    extensionMul c (1, 1) x = x := by
  rcases x with ⟨z, g⟩
  simp [extensionMul, mul_assoc]

theorem extensionMul_one_right
    {G Z : Type*} [Group G] [CommGroup Z]
    (c : NormalizedCocycle G Z) (x : Z × G) :
    extensionMul c x (1, 1) = x := by
  rcases x with ⟨z, g⟩
  simp [extensionMul, mul_assoc]

end ProjectiveRepresentation
end noncomputable section

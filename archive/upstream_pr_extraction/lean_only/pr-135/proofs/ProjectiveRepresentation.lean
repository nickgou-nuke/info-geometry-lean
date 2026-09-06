import proofs.ProjectiveUnitary6
import Mathlib.GroupTheory.QuotientGroup.Basic

noncomputable section
namespace ProjectiveRepresentation

structure NormalizedCocycle (G Z : Type*) [Group G] [CommGroup Z] where
  factor : G → G → Z
  left_one : ∀ g, factor 1 g = 1
  right_one : ∀ g, factor g 1 = 1
  cocycle : ∀ g h k,
    factor g h * factor (g * h) k = factor h k * factor g (h * k)

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

def quotientLift : G → (U ⧸ Subgroup.center U) :=
  fun g => QuotientGroup.mk' (Subgroup.center U) (ρ.lift g)

theorem quotientLift_one : quotientLift ρ 1 = 1 := by
  simp [quotientLift, ρ.lift_one]

theorem quotientLift_mul (g h : G) :
    quotientLift ρ (g * h) = quotientLift ρ g * quotientLift ρ h := by
  change QuotientGroup.mk' (Subgroup.center U) (ρ.lift (g * h)) =
    QuotientGroup.mk' (Subgroup.center U) (ρ.lift g) *
      QuotientGroup.mk' (Subgroup.center U) (ρ.lift h)
  calc
    QuotientGroup.mk' (Subgroup.center U) (ρ.lift (g * h)) =
        QuotientGroup.mk' (Subgroup.center U) (ρ.lift g * ρ.lift h) := by
          rw [ρ.map_mul]
          rw [QuotientGroup.mk'_eq_mk']
          refine ⟨(ι (ρ.factorSystem.factor g h) : U),
            (ι (ρ.factorSystem.factor g h)).property, ?_⟩
          exact (Semigroup.mem_center_iff.mp
            (ι (ρ.factorSystem.factor g h)).property) (ρ.lift (g * h))
    _ = QuotientGroup.mk' (Subgroup.center U) (ρ.lift g) *
        QuotientGroup.mk' (Subgroup.center U) (ρ.lift h) := by
          exact (QuotientGroup.mk' (Subgroup.center U)).map_mul
            (ρ.lift g) (ρ.lift h)

def quotientRepresentation : G →* (U ⧸ Subgroup.center U) where
  toFun := quotientLift ρ
  map_one' := quotientLift_one ρ
  map_mul' := quotientLift_mul ρ

end IsProjectiveRepresentation

def extensionMul {G Z : Type*} [Group G] [CommGroup Z]
    (c : NormalizedCocycle G Z) : (Z × G) → (Z × G) → (Z × G)
  | (z, g), (w, h) => (z * w * c.factor g h, g * h)

theorem extensionMul_assoc {G Z : Type*} [Group G] [CommGroup Z]
    (c : NormalizedCocycle G Z) (x y z : Z × G) :
    extensionMul c (extensionMul c x y) z =
      extensionMul c x (extensionMul c y z) := by
  rcases x with ⟨x, g⟩
  rcases y with ⟨y, h⟩
  rcases z with ⟨z, k⟩
  simp only [extensionMul, Prod.mk.injEq]
  constructor
  · calc
      x * y * c.factor g h * z * c.factor (g * h) k =
          x * y * z * (c.factor g h * c.factor (g * h) k) := by ac_rfl
      _ = x * y * z * (c.factor h k * c.factor g (h * k)) := by
        rw [c.cocycle]
      _ = x * (y * z * c.factor h k) * c.factor g (h * k) := by ac_rfl
  · simp [mul_assoc]

theorem extensionMul_one_left {G Z : Type*} [Group G] [CommGroup Z]
    (c : NormalizedCocycle G Z) (x : Z × G) :
    extensionMul c (1, 1) x = x := by
  rcases x with ⟨z, g⟩
  simp [extensionMul, c.left_one]

theorem extensionMul_one_right {G Z : Type*} [Group G] [CommGroup Z]
    (c : NormalizedCocycle G Z) (x : Z × G) :
    extensionMul c x (1, 1) = x := by
  rcases x with ⟨z, g⟩
  simp [extensionMul, c.right_one]

theorem factor_inv_symm {G Z : Type*} [Group G] [CommGroup Z]
    (c : NormalizedCocycle G Z) (g : G) :
    c.factor g g⁻¹ = c.factor g⁻¹ g := by
  have h := c.cocycle g g⁻¹ g
  simpa [c.left_one, c.right_one] using h

def extensionInv {G Z : Type*} [Group G] [CommGroup Z]
    (c : NormalizedCocycle G Z) : (Z × G) → (Z × G)
  | (z, g) => ((c.factor g g⁻¹)⁻¹ * z⁻¹, g⁻¹)

theorem extensionMul_left_inv {G Z : Type*} [Group G] [CommGroup Z]
    (c : NormalizedCocycle G Z) (x : Z × G) :
    extensionMul c (extensionInv c x) x = (1, 1) := by
  rcases x with ⟨z, g⟩
  simp [extensionMul, extensionInv, mul_assoc, factor_inv_symm]

theorem extensionMul_right_inv {G Z : Type*} [Group G] [CommGroup Z]
    (c : NormalizedCocycle G Z) (x : Z × G) :
    extensionMul c x (extensionInv c x) = (1, 1) := by
  rcases x with ⟨z, g⟩
  simp [extensionMul, extensionInv, mul_assoc, factor_inv_symm]

end ProjectiveRepresentation
end noncomputable section

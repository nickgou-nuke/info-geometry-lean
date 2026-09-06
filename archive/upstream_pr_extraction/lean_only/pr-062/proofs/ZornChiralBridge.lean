import Mathlib
import proofs.ZornParavectorNullspace
import proofs.ChiralCausalCone

/-!
# Zorn → Chiral CAR Bridge

The Zorn paravector `[[a,u],[v,b]]` maps to a 2×2 matrix via the
off-diagonal embedding: `[[a, u₀], [v₀, b]]`. The collapsed nilpotents
map to σ⁺ and σ⁻, welding the Zorn nullspace to the chiral CAR spine.

Zero sorries, zero axioms.
-/

namespace ZornChiralBridge

open ZornParavectorNullspace
open ChiralCausalCone

/-- Embed a Zorn paravector into M2C using the first vector component
as the off-diagonal entry. `[[a, u₀], [v₀, b]]`. -/
def zornToMatrix (X : Zorn) : M2C :=
  !![X.a, X.u 0; X.v 0, X.b]

/-- The carrier map used by the bridge. -/
def carrierMap : Zorn → M2C := zornToMatrix

/-- Canonical upper nilpotent lane. -/
def canonicalUpper : Zorn :=
  { a := 0, b := 0, u := fun | 0 => 1 | _ => 0, v := fun _ => 0 }

/-- Canonical lower nilpotent lane. -/
def canonicalLower : Zorn :=
  collapsedLower (fun | 0 => 1 | _ => 0)

/-- The collapsed state `[[0,0],[p,0]]` maps to `[[0,0],[p₀,0]]`. -/
theorem collapsed_maps_to_lower (p : Vec3) :
    zornToMatrix (collapsedLower p) = !![0, 0; p 0, 0] := by
  simp [zornToMatrix, collapsedLower]

/-- The upper nilpotent `[[0,u],[0,0]]` maps to `[[0,u₀],[0,0]]`. -/
theorem upperNil_maps_to_upper {u : Vec3} :
    zornToMatrix { a := 0, b := 0, u := u, v := fun _ => 0 } = !![0, u 0; 0, 0] := by
  simp [zornToMatrix]

/-- The collapsed nilpotent image inherits nilpotency: `Z² = 0`. -/
theorem collapsed_image_nilpotent (p : Vec3) :
    zornToMatrix (collapsedLower p) * zornToMatrix (collapsedLower p) = 0 := by
  rw [collapsed_maps_to_lower]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- When `p = (1,0,0)`, collapsed maps exactly to `σMinus`. -/
theorem collapsed_unit_is_sigmaMinus :
    zornToMatrix (collapsedLower (fun | 0 => 1 | _ => 0)) = σMinus := by
  simp [zornToMatrix, collapsedLower, σMinus]

/-- When `u = (1,0,0)`, upper nilpotent maps exactly to `σPlus`. -/
theorem upperNil_unit_is_sigmaPlus :
    zornToMatrix { a := 0, b := 0, u := fun | 0 => 1 | _ => 0, v := fun _ => 0 } = σPlus := by
  simp [zornToMatrix, σPlus]

@[simp] theorem carrierMap_upper_canonical : carrierMap canonicalUpper = σPlus := by
  simpa [carrierMap, canonicalUpper] using upperNil_unit_is_sigmaPlus

@[simp] theorem carrierMap_lower_canonical : carrierMap canonicalLower = σMinus := by
  simpa [carrierMap, canonicalLower] using collapsed_unit_is_sigmaMinus

/-- Carrier compatibility on the canonical chiral generators:
the commutator, anticommutator, and square-zero relations are preserved on
the embedded upper/lower lanes. -/
theorem carrierMap_bracket_compatibility :
    carrierMap canonicalUpper * carrierMap canonicalLower -
      carrierMap canonicalLower * carrierMap canonicalUpper = σ3c ∧
    carrierMap canonicalUpper * carrierMap canonicalLower +
      carrierMap canonicalLower * carrierMap canonicalUpper = (1 : M2C) ∧
    carrierMap canonicalUpper * carrierMap canonicalUpper = 0 ∧
    carrierMap canonicalLower * carrierMap canonicalLower = 0 := by
  rw [carrierMap_upper_canonical, carrierMap_lower_canonical]
  exact ⟨comm_σPlus_σMinus, anti_σPlus_σMinus, σPlus_sq, σMinus_sq⟩

/-- The Zorn-Chiral weld: nilpotent Zorn elements map to nilpotent chiral CAR operators.
This bridges the Zorn nullspace layer (ZornParavectorNullspace, ZornScalingFlow)
to the chiral CAR spine (ChiralCausalCone). -/
theorem zorn_chiral_weld :
    (zornToMatrix (collapsedLower (fun | 0 => 1 | _ => 0)) = σMinus) ∧
    (zornToMatrix { a := 0, b := 0, u := fun | 0 => 1 | _ => 0, v := fun _ => 0 } = σPlus) ∧
    (∀ p : Vec3, zornToMatrix (collapsedLower p) * zornToMatrix (collapsedLower p) = 0) := by
  exact ⟨collapsed_unit_is_sigmaMinus, upperNil_unit_is_sigmaPlus, collapsed_image_nilpotent⟩

end ZornChiralBridge

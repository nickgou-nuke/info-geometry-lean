/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.CotangentLieForm
import Mathlib.LinearAlgebra.FixedSubmodule
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# A fixed cotangent locus need not be symplectic

The real shear `(x,y) ↦ (x+y,y)` fixes the first coordinate axis. Its
contragredient fixes the second coordinate covectors. Their pairing is zero,
so the two-dimensional fixed phase space has identically zero restricted
canonical form. This is a counterexample to the unrestricted fixed-locus
claim; finite symmetry restores nondegeneracy in `FiniteCotangentInvariants`.
-/

noncomputable section

namespace InfoGeometry.Geometry.CotangentFixedShear

open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Canonical.SouriauContragredientPairing
open InfoGeometry.Geometry.CotangentLieForm

/-- An actual real linear shear automorphism. -/
def shear : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun v := (v.1 + v.2, v.2)
  invFun v := (v.1 - v.2, v.2)
  left_inv := by intro v; ext <;> simp
  right_inv := by intro v; ext <;> simp
  map_add' := by intro v w; ext <;> simp <;> ring
  map_smul' := by intro r v; ext <;> simp [mul_add]

theorem shear_fixed_iff (v : ℝ × ℝ) : shear v = v ↔ v.2 = 0 := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    change v.1 + v.2 = v.1 at h1
    linarith
  · intro h
    ext <;> simp [shear, h]

/-- Coordinates of an actual algebraic covector, derived from linearity. -/
theorem dual_coordinates (α : Module.Dual ℝ (ℝ × ℝ)) (v : ℝ × ℝ) :
    α v = v.1 * α (1, 0) + v.2 * α (0, 1) := by
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by ext <;> simp
  calc
    α v = α (v.1 • (1, 0) + v.2 • (0, 1)) := congrArg α hv
    _ = v.1 * α (1, 0) + v.2 * α (0, 1) := by
      simp only [map_add, map_smul, smul_eq_mul]

theorem shear_dual_fixed_iff (α : Module.Dual ℝ (ℝ × ℝ)) :
    contragredient shear α = α ↔ α (1, 0) = 0 := by
  constructor
  · intro h
    have h2 := congrArg (fun f : Module.Dual ℝ (ℝ × ℝ) => f (0, 1)) h
    change α (0 - 1, 1) = α (0, 1) at h2
    rw [zero_sub] at h2
    rw [dual_coordinates α (-1, 1)] at h2
    norm_num at h2
    linarith
  · intro h
    apply LinearMap.ext
    intro v
    change α (v.1 - v.2, v.2) = α v
    rw [dual_coordinates α (v.1 - v.2, v.2), dual_coordinates α v]
    simp [h]

/-- The native fixed vector submodule. -/
def fixedPrimal : Submodule ℝ (ℝ × ℝ) := shear.toLinearMap.fixedSubmodule

/-- The native fixed covector submodule. -/
def fixedDual : Submodule ℝ (Module.Dual ℝ (ℝ × ℝ)) :=
  (contragredient shear).fixedSubmodule

theorem fixed_pairing_zero (x : fixedPrimal) (α : fixedDual) : α.1 x.1 = 0 := by
  have hx := (shear_fixed_iff x.1).mp x.property
  have hα := (shear_dual_fixed_iff α.1).mp α.property
  rw [dual_coordinates]
  simp [hx, hα]

/-- The fixed vectors are exactly the first coordinate axis. -/
def fixedPrimalEquiv : ℝ ≃ₗ[ℝ] fixedPrimal where
  toFun a := ⟨(a, 0), (shear_fixed_iff _).mpr rfl⟩
  invFun x := x.1.1
  left_inv := by intro a; rfl
  right_inv := by
    intro x
    apply Subtype.ext
    exact Prod.ext rfl ((shear_fixed_iff x.1).mp x.property).symm
  map_add' := by
    intro a b
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp
  map_smul' := by
    intro r a
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp

/-- The fixed covectors are exactly multiples of the second coordinate covector. -/
def fixedDualEquiv : ℝ ≃ₗ[ℝ] fixedDual where
  toFun a := ⟨a • LinearMap.snd ℝ ℝ ℝ,
    (shear_dual_fixed_iff _).mpr (by simp)⟩
  invFun α := α.1 (0, 1)
  left_inv := by intro a; simp
  right_inv := by
    intro α
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    have hα := (shear_dual_fixed_iff α.1).mp α.property
    rw [dual_coordinates α.1 v]
    simp [hα, mul_comm]
  map_add' := by intros; apply Subtype.ext; simp [add_smul]
  map_smul' := by intros; apply Subtype.ext; simp [smul_smul]

/-- The fixed phase carrier is genuinely two-dimensional. -/
theorem fixed_phase_finrank : Module.finrank ℝ (fixedPrimal × fixedDual) = 2 := by
  have h := (fixedPrimalEquiv.prodCongr fixedDualEquiv).finrank_eq
  simpa using h.symm

def fixedPhaseInclusion : (fixedPrimal × fixedDual) →ₗ[ℝ] PhaseSpaceCarrier (ℝ × ℝ) :=
  fixedPrimal.subtype.prodMap fixedDual.subtype

/-- The actual restriction of the ambient canonical form. -/
def fixedOmega : LinearMap.BilinForm ℝ (fixedPrimal × fixedDual) :=
  (neutralOmega (E := ℝ × ℝ)).compl₁₂ fixedPhaseInclusion fixedPhaseInclusion

/-- The entire restricted form vanishes, not merely one pairing. -/
theorem fixedOmega_eq_zero : fixedOmega = 0 := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro w
  change neutralOmega (fixedPhaseInclusion z) (fixedPhaseInclusion w) = 0
  rw [neutralOmega_apply]
  change w.2.1 z.1.1 - z.2.1 w.1.1 = 0
  rw [fixed_pairing_zero, fixed_pairing_zero, sub_self]

/-- A concrete nonzero radical vector disproves nondegeneracy. -/
theorem fixedOmega_not_nondegenerate : ¬fixedOmega.Nondegenerate := by
  intro h
  have hz := h.1 (fixedPrimalEquiv 1, 0) (by intro w; rw [fixedOmega_eq_zero]; rfl)
  have h1 := congrArg (fun z : fixedPrimal × fixedDual => z.1.1.1) hz
  norm_num [fixedPrimalEquiv] at h1

/-- The natural restriction map also vanishes in this counterexample. -/
theorem fixed_dual_restriction_zero (α : fixedDual) :
    α.1.comp fixedPrimal.subtype = 0 := by
  apply LinearMap.ext
  intro x
  exact fixed_pairing_zero x α

end InfoGeometry.Geometry.CotangentFixedShear

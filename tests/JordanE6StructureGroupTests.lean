/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.H3ZornStructureGroup
import InfoGeometry.Algebra.H3ZornReducedStructureLieAlgebra
import InfoGeometry.Algebra.H3ZornOperatorNoncommutativity

/-!
# Semantic Regression Tests for `Str(H₃(𝕆_s))`, `Str₀(H₃(𝕆_s))`, and 78D `h3zornCubicStabilizer`

Exercises non-diagonal invertible elements of `H3Zorn ℝ` (with `N(x) = ±1`)
acting via `U x` inside `StructureGroup ℝ (H3Zorn ℝ)` and `h3zornReducedStructureGroup`,
confirms strict containment `Aut(H₃(𝕆_s)) ⊂ Str₀(H₃(𝕆_s))`, and verifies
non-commuting elements of `h3zornCubicStabilizer` across both `H3ZornF4Derivations`
and `L(H₃⁰)`.
-/

namespace InfoGeometry.Tests.JordanE6StructureGroup

open InfoGeometry.Algebra InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Canonical.H3ZornF4PeirceTrialitySplit

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Non-diagonal invertible element with `N(xPos) = 1`. -/
noncomputable def xPos : H3Zorn ℝ :=
  { α₁ := 1, α₂ := 1, α₃ := 1, a := ZornVectorMatrix.E11, b := 0, c := 0 }

/-- Non-diagonal invertible element with `N(xNeg) = -1`. -/
noncomputable def xNeg : H3Zorn ℝ :=
  { α₁ := -1, α₂ := 1, α₃ := 1, a := ZornVectorMatrix.E11, b := 0, c := 0 }

theorem xPos_a_ne_zero : xPos.a ≠ 0 := by
  intro h
  have ha := congrArg ZornVectorMatrix.a h
  change (1 : ℝ) = 0 at ha
  norm_num at ha

theorem xNeg_a_ne_zero : xNeg.a ≠ 0 := by
  intro h
  have ha := congrArg ZornVectorMatrix.a h
  change (1 : ℝ) = 0 at ha
  norm_num at ha

theorem normCubic_xPos : normCubic xPos = 1 := by
  simp [xPos, normCubic, ZornVectorMatrix.norm, ZornVectorMatrix.E11,
    ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVec3.dot]

theorem normCubic_xNeg : normCubic xNeg = -1 := by
  simp [xNeg, normCubic, ZornVectorMatrix.norm, ZornVectorMatrix.E11,
    ZornVectorMatrix.trace, ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVec3.dot]

theorem xPos_norm_ne_zero : normCubic xPos ≠ 0 := by
  rw [normCubic_xPos]; norm_num

theorem xNeg_norm_ne_zero : normCubic xNeg ≠ 0 := by
  rw [normCubic_xNeg]; norm_num

theorem U_xPos_mem_StructureGroup :
    h3zornULinearEquiv xPos xPos_norm_ne_zero ∈ StructureGroup ℝ (H3Zorn ℝ) :=
  h3zornULinearEquiv_mem_StructureGroup xPos xPos_norm_ne_zero

theorem U_xNeg_mem_StructureGroup :
    h3zornULinearEquiv xNeg xNeg_norm_ne_zero ∈ StructureGroup ℝ (H3Zorn ℝ) :=
  h3zornULinearEquiv_mem_StructureGroup xNeg xNeg_norm_ne_zero

theorem U_xPos_mem_reducedStructureGroup :
    h3zornULinearEquiv xPos xPos_norm_ne_zero ∈ h3zornReducedStructureGroup :=
  h3zornULinearEquiv_mem_reducedStructureGroup xPos xPos_norm_ne_zero
    (Or.inl normCubic_xPos)

theorem U_xNeg_mem_reducedStructureGroup :
    h3zornULinearEquiv xNeg xNeg_norm_ne_zero ∈ h3zornReducedStructureGroup :=
  h3zornULinearEquiv_mem_reducedStructureGroup xNeg xNeg_norm_ne_zero
    (Or.inr normCubic_xNeg)

theorem U_xPos_multiplier_eq_one :
    h3zornStructureGroupMultiplier
        ⟨h3zornULinearEquiv xPos xPos_norm_ne_zero, U_xPos_mem_StructureGroup⟩ = 1 := by
  apply Units.ext
  rw [h3zornStructureGroupMultiplier_val, h3zornULinearEquiv_apply,
    normCubic_U, normCubic_xPos, normCubic_one]
  norm_num

theorem U_xNeg_multiplier_eq_one :
    h3zornStructureGroupMultiplier
        ⟨h3zornULinearEquiv xNeg xNeg_norm_ne_zero, U_xNeg_mem_StructureGroup⟩ = 1 := by
  apply Units.ext
  rw [h3zornStructureGroupMultiplier_val, h3zornULinearEquiv_apply,
    normCubic_U, normCubic_xNeg, normCubic_one]
  norm_num

/-- `U xPos` preserves the cubic norm (`∈ Str₀`) but moves the identity `1`,
showing `Aut(H₃(𝕆_s))` is strictly smaller than `Str₀(H₃(𝕆_s))`. -/
theorem U_xPos_moves_one :
    h3zornULinearEquiv xPos xPos_norm_ne_zero 1 ≠ 1 := by
  intro h
  have ha := congrArg (fun W : H3Zorn ℝ => W.a.a) h
  rw [h3zornULinearEquiv_apply] at ha
  have hval : (U xPos 1).a.a = 2 := by
    simp [xPos, U, traceBilin, H3Zorn.crossProduct, adjointQuad,
      sub_readback, smul_readback, one_readback,
      ZornVectorMatrix.E11, ZornVectorMatrix.norm, ZornVectorMatrix.conj,
      ZornVectorMatrix.mul, ZornVectorMatrix.sub, ZornVectorMatrix.add,
      ZornVectorMatrix.smul, ZornVectorMatrix.neg, ZornVectorMatrix.trace,
      ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]
    norm_num
  rw [hval] at ha
  change (2 : ℝ) = 0 at ha
  norm_num at ha

theorem off12_mem_traceZero : h3_off₁₂ 1 ∈ h3zornTraceZero := by
  simp [h3_off₁₂, linearTrace]

theorem off23_mem_traceZero : h3_off₂₃ 2 ∈ h3zornTraceZero := by
  simp [h3_off₂₃, linearTrace]

theorem diagDiff_mem_traceZero : h3_diag₁ - h3_diag₂ ∈ h3zornTraceZero := by
  simp [h3_diag₁, h3_diag₂, sub_readback, linearTrace]

theorem noncommuting_Lmul_in_cubicStabilizer :
    jordanLmul (R := ℝ) (h3_off₁₂ 1) ∈ h3zornCubicStabilizer ∧
    jordanLmul (R := ℝ) (h3_off₂₃ 2) ∈ h3zornCubicStabilizer ∧
    ⁅jordanLmul (R := ℝ) (h3_off₁₂ 1), jordanLmul (R := ℝ) (h3_off₂₃ 2)⁆ ∈
      h3zornCubicStabilizer ∧
    ⁅jordanLmul (R := ℝ) (h3_off₁₂ 1), jordanLmul (R := ℝ) (h3_off₂₃ 2)⁆ ≠ 0 := by
  have h1 : jordanLmul (R := ℝ) (h3_off₁₂ 1) ∈ h3zornCubicStabilizer :=
    (jordanLmul_mem_h3zornCubicStabilizer_iff _).mpr off12_mem_traceZero
  have h2 : jordanLmul (R := ℝ) (h3_off₂₃ 2) ∈ h3zornCubicStabilizer :=
    (jordanLmul_mem_h3zornCubicStabilizer_iff _).mpr off23_mem_traceZero
  refine ⟨h1, h2, h3zornCubicStabilizer.lie_mem h1 h2, ?_⟩
  exact h3Zorn_offDiagonal_innerDerivation_ne_zero

theorem noncommuting_F4_and_Lmul_in_cubicStabilizer :
    (f4Basis 0).1 ∈ h3zornCubicStabilizer ∧
    jordanLmul (R := ℝ) (h3_diag₁ - h3_diag₂) ∈ h3zornCubicStabilizer ∧
    ⁅(f4Basis 0).1, jordanLmul (R := ℝ) (h3_diag₁ - h3_diag₂)⁆ ∈
      h3zornCubicStabilizer ∧
    ⁅(f4Basis 0).1, jordanLmul (R := ℝ) (h3_diag₁ - h3_diag₂)⁆ ≠ 0 := by
  have hF4 : (f4Basis 0).1 ∈ h3zornCubicStabilizer :=
    H3ZornF4Derivations_le_h3zornCubicStabilizer (f4Basis 0).property
  have hL : jordanLmul (R := ℝ) (h3_diag₁ - h3_diag₂) ∈ h3zornCubicStabilizer :=
    (jordanLmul_mem_h3zornCubicStabilizer_iff _).mpr diagDiff_mem_traceZero
  refine ⟨hF4, hL, h3zornCubicStabilizer.lie_mem hF4 hL, ?_⟩
  intro hzero
  have hlie : ⁅(f4Basis 0).1, jordanLmul (R := ℝ) (h3_diag₁ - h3_diag₂)⁆ =
      jordanLmul (R := ℝ) ((f4Basis 0).1 (h3_diag₁ - h3_diag₂)) :=
    lie_derivation_jordanLmul (f4Basis 0).1 (f4Basis 0).property (h3_diag₁ - h3_diag₂)
  rw [hlie] at hzero
  have h1 := LinearMap.ext_iff.mp hzero (1 : H3Zorn ℝ)
  change candidateJordanMul ((f4Basis 0).1 (h3_diag₁ - h3_diag₂)) 1 = 0 at h1
  rw [candidateJordanMul_one_right] at h1
  have ha := congrArg (fun W : H3Zorn ℝ => W.a.a) h1
  have hcalc : ((f4Basis 0).1 (h3_diag₁ - h3_diag₂)).a.a = -(1 / 2 : ℝ) := by
    have hf0 : (f4Basis 0).1 (h3_diag₁ - h3_diag₂) =
        h3_diag₁ * (embedJ12 (zorn_basis 0) * (h3_diag₁ - h3_diag₂)) -
          embedJ12 (zorn_basis 0) * (h3_diag₁ * (h3_diag₁ - h3_diag₂)) := rfl
    rw [hf0, mul_sub, mul_sub, mul_sub, h3_diag₁_mul_h3_diag₁, h3_diag₁_mul_h3_diag₂, sub_zero,
      mul_comm (embedJ12 (zorn_basis 0)) h3_diag₁,
      mul_comm (embedJ12 (zorn_basis 0)) h3_diag₂,
      h3_diag₁_mul_embedJ12, h3_diag₂_mul_embedJ12, sub_self, zero_sub]
    simp [embedJ12, neg_readback, smul_readback, ZornVectorMatrix.neg,
      ZornVectorMatrix.smul, zorn_basis]
  rw [hcalc] at ha
  change -(1 / 2 : ℝ) = 0 at ha
  norm_num at ha

end InfoGeometry.Tests.JordanE6StructureGroup

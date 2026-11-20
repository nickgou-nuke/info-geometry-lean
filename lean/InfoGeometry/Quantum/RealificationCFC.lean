/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.RealificationStates
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Actual functional calculus in the internal-complex real matrix sector

The existing block realification is a continuous real star-algebra homomorphism.
Consequently the native matrix exponential and continuous functional calculus
commute with it. Strict positivity is preserved and reflected, and the native
inverse, logarithm, and positive square root are transported without supplied
compatibility witnesses.

The order and adjoint here are the ordinary Hilbert-space matrix order and
transpose. No indefinite Krein adjoint is used to define a positive logarithm.
The codomain of the homomorphism is a doubled real matrix algebra; its image is
the existing centralizer of `internalJ`, not the entire doubled algebra.
-/

noncomputable section

open Matrix
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace InfoGeometry.Quantum.Realification

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "CMat" => Matrix n n ℂ
local notation "RMat" => Matrix (n ⊕ n) (n ⊕ n) ℝ

/-- The unital encoding of operators, distinct from the trace-one state map. -/
def realifyStarAlgHom : CMat →⋆ₐ[ℝ] RMat where
  toFun := realify
  map_zero' := realify_zero
  map_one' := realify_one
  map_add' := realify_add
  map_mul' := realify_mul
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, realify_smul, realify_one]
  map_star' A := realify_star A

@[simp] theorem realifyStarAlgHom_apply (A : CMat) :
    realifyStarAlgHom A = realify A := rfl

omit [DecidableEq n] in
/-- Finite-dimensional real linearity supplies the actual continuity proof. -/
theorem continuous_realify : Continuous (realify (m := n) (n := n)) :=
  (realifyLinearMap (m := n) (n := n)).continuous_of_finiteDimensional

omit [DecidableEq n] in
/-- Native Hilbert positivity is reflected as well as preserved. -/
theorem realify_nonneg_iff (A : CMat) : 0 ≤ realify A ↔ 0 ≤ A := by
  simpa only [Matrix.nonneg_iff_posSemidef] using realify_posSemidef_iff A

/-- Faithful positive matrices remain faithful after realification, and conversely. -/
theorem realify_posDef_iff (A : CMat) : (realify A).PosDef ↔ A.PosDef := by
  constructor
  · intro hA
    have hpos := (realify_posSemidef_iff A).mp hA.posSemidef
    refine PosDef.of_dotProduct_mulVec_pos hpos.isHermitian fun z hz => ?_
    have hreal : realifyVector z ≠ 0 := by
      intro hzero
      apply hz
      have hzero' : unrealifyVector (0 : n ⊕ n → ℝ) = 0 := by
        funext i
        rfl
      have h := congrArg unrealifyVector hzero
      simpa only [unrealifyVector_realifyVector, hzero'] using h
    apply Complex.pos_iff.mpr
    constructor
    · simpa only [quadratic_realify] using hA.dotProduct_mulVec_pos hreal
    · exact (Complex.nonneg_iff.mp (hpos.dotProduct_mulVec_nonneg z)).2
  · intro hA
    apply ((realify_posSemidef_iff A).mpr hA.posSemidef).posDef_iff_isUnit.mpr
    exact hA.isUnit.map realifyRingHom

theorem realify_isStrictlyPositive_iff (A : CMat) :
    IsStrictlyPositive (realify A) ↔ IsStrictlyPositive A := by
  simpa only [Matrix.isStrictlyPositive_iff_posDef] using realify_posDef_iff A

/-- The native nonsingular inverse is transported for every invertible matrix. -/
theorem realify_inv (A : CMat) (hA : IsUnit A) :
    realify A⁻¹ = (realify A)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← realify_mul, Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA), realify_one]

/-- Naturality for the native real continuous functional calculus. -/
theorem realify_cfc (f : ℝ → ℝ) (A : CMat)
    (hf : ContinuousOn f (spectrum ℝ A)) (hA : IsSelfAdjoint A) :
    realify (cfc f A) = cfc f (realify A) := by
  exact StarAlgHomClass.map_cfc realifyStarAlgHom f A hf continuous_realify hA
    (hA.map realifyStarAlgHom)

/-- The actual logarithm transports on the faithful positive cone. -/
theorem realify_log (A : CMat) (hA : IsStrictlyPositive A) :
    realify (CFC.log A) = CFC.log (realify A) := by
  have hf : ContinuousOn Real.log (spectrum ℝ A) := by
    apply Real.continuousOn_log.mono
    intro x hx
    exact ne_of_gt (hA.spectrum_pos hx)
  exact realify_cfc Real.log A hf hA.isSelfAdjoint

/-- Positive square roots transport through the native non-unital calculus. -/
theorem realify_sqrt (A : CMat) (hA : 0 ≤ A) :
    realify (CFC.sqrt A) = CFC.sqrt (realify A) := by
  have hR : 0 ≤ realify A := (realify_nonneg_iff A).mpr hA
  rw [CFC.sqrt_eq_real_sqrt A hA, CFC.sqrt_eq_real_sqrt (realify A) hR]
  exact NonUnitalStarAlgHomClass.map_cfcₙ
    realifyStarAlgHom.toNonUnitalStarAlgHom Real.sqrt A
    Real.continuous_sqrt.continuousOn Real.sqrt_zero continuous_realify
    hA.isSelfAdjoint hR.isSelfAdjoint

section Exponential

-- The matrix norm is the existing L2 operator norm. Restricting its scalar
-- field supplies the rational normed algebra needed by the native exponential.
local instance {m : Type*} [Fintype m] [DecidableEq m] :
    NormedAlgebra ℚ (Matrix m m ℂ) where
  norm_smul_le r A := by
    rw [← IsScalarTower.algebraMap_smul ℂ r A]
    simpa only [norm_algebraMap'] using (norm_smul_le (algebraMap ℚ ℂ r) A)

/-- The actual exponential transports for every matrix, without selfadjointness. -/
theorem realify_exp (A : CMat) :
    realify (NormedSpace.exp A) = NormedSpace.exp (realify A) := by
  exact NormedSpace.map_exp realifyRingHom continuous_realify A

end Exponential

/-- The ordinary trace-one encoding preserves faithful Hilbert positivity. -/
theorem state_isStrictlyPositive {ρ : CMat} (hρ : IsStrictlyPositive ρ) :
    IsStrictlyPositive (state ρ) :=
  IsStrictlyPositive.smul (by norm_num : (0 : ℝ) < 1 / 2)
    ((realify_isStrictlyPositive_iff ρ).mpr hρ)

/-- The factor one half in the state map contributes a central `-log 2`. -/
theorem log_state (ρ : CMat) (hρ : IsStrictlyPositive ρ) :
    CFC.log (state ρ) = realify (CFC.log ρ) - Real.log 2 • (1 : RMat) := by
  rw [state, CFC.log_smul' (realify ρ) (by norm_num : (0 : ℝ) < 1 / 2)
    ((realify_isStrictlyPositive_iff ρ).mpr hρ), ← realify_log ρ hρ]
  simp only [one_div, Real.log_inv, map_neg, Algebra.algebraMap_eq_smul_one]
  abel

/-- Square-root state vectors carry a factor `sqrt (1/2)`, distinct from both
the unital operator encoding and the density encoding's factor `1/2`. -/
theorem sqrt_state (ρ : CMat) (hρ : 0 ≤ ρ) :
    CFC.sqrt (state ρ) = Real.sqrt (1 / 2) • realify (CFC.sqrt ρ) := by
  have hsqrt : 0 ≤ realify (CFC.sqrt ρ) :=
    (realify_nonneg_iff _).mpr (CFC.sqrt_nonneg ρ)
  have hscaled : 0 ≤ Real.sqrt (1 / 2) • realify (CFC.sqrt ρ) :=
    (hsqrt.posSemidef.smul (Real.sqrt_nonneg _)).nonneg
  apply CFC.sqrt_unique (hb := hscaled)
  rw [smul_mul_smul, ← realify_mul, CFC.sqrt_mul_sqrt_self ρ hρ,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rfl

/-- The inverse state has the reciprocal normalization factor. -/
theorem inv_state (ρ : CMat) (hρ : IsUnit ρ) :
    (state ρ)⁻¹ = (2 : ℝ) • realify ρ⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [state, smul_mul_smul, ← realify_mul, Matrix.mul_nonsing_inv ρ
    ((Matrix.isUnit_iff_isUnit_det ρ).mp hρ), realify_one]
  norm_num

end InfoGeometry.Quantum.Realification

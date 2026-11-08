/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MatrixStageProductDensityPositive

/-! # Product functionals on the native algebraic matrix colimit

Normalization and positivity descend through the existing direct-limit lift.
No completion or full Cuntz KMS identity is asserted here.
-/
noncomputable section
namespace InfoGeometry.QuantumContext.MatrixStageProductDensity

open InfoGeometry.Canonical
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.QuantumContext.MatrixStagePartialTrace

theorem density_weightedCompatible (q : Fin 2 → ℝ) (hq : q 0 + q 1 = 1) :
    WeightedCompatible (density (fun i => (q i : ℂ))) :=
  weightedStageFunctional_compatible_of_partialTraceCompatible _
    (density_compatible _ (by exact_mod_cast hq))

/-- The product-density functional, using the canonical matrix-colimit lift. -/
def productFunctional (q : Fin 2 → ℝ) (hq : q 0 + q 1 = 1) :
    CuntzMatrixCompatibleStateNet.Carrier →ₗ[ℂ] ℂ :=
  weightedColimitFunctional (density (fun i => (q i : ℂ)))
    (density_weightedCompatible q hq)

theorem productFunctional_one (q : Fin 2 → ℝ) (hq : q 0 + q 1 = 1) :
    productFunctional q hq 1 = 1 := by
  exact weightedColimitFunctional_one _ (density_weightedCompatible q hq)
    (fun n => density_trace_one _ (by exact_mod_cast hq) n)

/-- Positivity holds on every star-square in the full algebraic colimit. -/
theorem productFunctional_positive (q : Fin 2 → ℝ) (hq : q 0 + q 1 = 1)
    (hpos : ∀ i, 0 ≤ q i) (X : CuntzMatrixCompatibleStateNet.Carrier) :
    0 ≤ (productFunctional q hq (star X * X)).re := by
  exact weightedColimitFunctional_positive _ (density_weightedCompatible q hq)
    (density_stage_positive q hpos) X

/-- Finite observables retain their weighted normalized trace after descent. -/
theorem productFunctional_stage (q : Fin 2 → ℝ) (hq : q 0 + q 1 = 1)
    (n : ℕ) (X : MatrixStage n) :
    productFunctional q hq (stageInjection n X) =
      matrixTraceFunctional n (X * density (fun i => (q i : ℂ)) n) := by
  exact weightedColimitFunctional_stage _ (density_weightedCompatible q hq) n X

/-- Matrix-unit readout: off-diagonal units vanish and diagonal units recover
the normalized product density weight. -/
theorem productFunctional_matrixUnit (q : Fin 2 → ℝ) (hq : q 0 + q 1 = 1)
    (n : ℕ) (i j : Fin (2 ^ n)) :
    productFunctional q hq (stageInjection n (Matrix.single i j (1 : ℂ))) =
      if i = j then (1 / (2 ^ n : ℂ)) * (diagonalWeight q n i : ℂ) else 0 := by
  rw [productFunctional_stage, matrixTraceFunctional_apply, Matrix.trace_single_mul,
    density_eq_diagonal]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

theorem productFunctional_star (q : Fin 2 → ℝ) (hq : q 0 + q 1 = 1)
    (X : CuntzMatrixCompatibleStateNet.Carrier) :
    productFunctional q hq (star X) = star (productFunctional q hq X) := by
  unfold productFunctional weightedColimitFunctional
  have hn : normalizedWeightedStageFunctional (density (fun i => (q i : ℂ))) 1 =
      weightedStageFunctional (density (fun i => (q i : ℂ))) := by
    funext n
    simp [normalizedWeightedStageFunctional]
  simpa only [normalizedWeightedColimitFunctional, hn] using
    normalizedWeightedColimitFunctional_star _ 1 (density_weightedCompatible q hq)
      (density_star q) X

open scoped ComplexOrder in
/-- Complex-order positivity includes vanishing imaginary part. -/
theorem productFunctional_nonneg (q : Fin 2 → ℝ) (hq : q 0 + q 1 = 1)
    (hpos : ∀ i, 0 ≤ q i) (X : CuntzMatrixCompatibleStateNet.Carrier) :
    0 ≤ productFunctional q hq (star X * X) := by
  apply Complex.nonneg_iff.mpr
  refine ⟨productFunctional_positive q hq hpos X, ?_⟩
  have hs : star (productFunctional q hq (star X * X)) =
      productFunctional q hq (star X * X) := by
    rw [← productFunctional_star]
    simp
  have hi := congrArg Complex.im hs
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

end InfoGeometry.QuantumContext.MatrixStageProductDensity
end

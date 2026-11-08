/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.AlgebraicKMSStateColimit

/-!
# Positivity of the normalized propagated Gibbs KMS functional

This file closes the remaining state-level gap for the concrete propagated
Gibbs density: the existing owner proves normalization, the algebraic KMS
boundary identity, and positivity of the unnormalized weighted functional.
Here the finite partition function is shown to be a strictly positive real
normalizer, and that result is used to transfer positivity through the actual
normalized colimit functional.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.AlgebraicKMSStateColimit

open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
open InfoGeometry.Canonical.CuntzMatrixCompatibleStateNet
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
open scoped MatrixOrder ComplexOrder

theorem propagatedGibbsDensity_normalizer_real_pos
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) :
    0 < (traceFunctional
      (densityColimitUnit
        (propagatedGibbsDensity H₀ h₀ β)
        (propagatedGibbsDensity_unit_zero H₀ h₀ β) : Carrier)).re := by
  let D : MatrixStage 0 := gibbsDensity
    (propagatedHamiltonian H₀ 0)
    (propagatedHamiltonian_isHermitian H₀ h₀ 0) β
  have hD := Matrix.nonneg_iff_posSemidef.mp
    (gibbsDensity_nonneg
      (propagatedHamiltonian H₀ 0)
      (propagatedHamiltonian_isHermitian H₀ h₀ 0) β)
  have htrace_nonneg : 0 ≤ (Matrix.trace D).re :=
    (RCLike.nonneg_iff.mp hD.trace_nonneg).1
  have htrace_ne : Matrix.trace D ≠ 0 := by
    exact gibbsPartition_ne_zero
      (propagatedHamiltonian H₀ 0)
      (propagatedHamiltonian_isHermitian H₀ h₀ 0) β
  have hDself : star D = D := by
    simpa [D] using
      (gibbsDensity_isHermitian
        (propagatedHamiltonian H₀ 0)
        (propagatedHamiltonian_isHermitian H₀ h₀ 0) β).star_eq
  have htrace_im : (Matrix.trace D).im = 0 := by
    have hconj : star (Matrix.trace D) = Matrix.trace D := by
      calc
        star (Matrix.trace D) = Matrix.trace (star D) := by
          rw [← Matrix.trace_conjTranspose]
          rfl
        _ = Matrix.trace D := congrArg Matrix.trace hDself
    exact Complex.conj_eq_iff_im.mp (by simpa [Complex.star_def] using hconj)
  have htrace_re_ne : (Matrix.trace D).re ≠ 0 := by
    intro hzero
    apply htrace_ne
    exact Complex.ext hzero htrace_im
  have htrace_pos : 0 < (Matrix.trace D).re :=
    lt_of_le_of_ne htrace_nonneg htrace_re_ne.symm
  rw [densityColimitUnit_coe, traceFunctional_stage,
    matrixTraceState_apply]
  norm_num at htrace_pos ⊢
  change 0 < (Matrix.trace D).re
  exact htrace_pos

theorem propagatedGibbsDensity_normalized_positive
    (H₀ : MatrixStage 0) (h₀ : H₀.IsHermitian) (β : ℝ) (x : Carrier) :
    0 ≤
      (normalizedDeltaWeightedFunctional
        (densityColimitUnit
          (propagatedGibbsDensity H₀ h₀ β)
          (propagatedGibbsDensity_unit_zero H₀ h₀ β))
        (star x * x)).re := by
  let D := propagatedGibbsDensity H₀ h₀ β
  let hD : DensityCompatible D := propagatedGibbsDensity_compatible H₀ h₀ β
  let δ := densityColimitUnit D (propagatedGibbsDensity_unit_zero H₀ h₀ β)
  let z : ℝ := (traceFunctional (δ : Carrier)).re
  have hz : 0 < z := by
    exact propagatedGibbsDensity_normalizer_real_pos H₀ h₀ β
  have him : (traceFunctional (δ : Carrier)).im = 0 := by
    rw [densityColimitUnit_coe, traceFunctional_stage, matrixTraceState_apply]
    have hDself : star (propagatedGibbsDensity H₀ h₀ β 0) =
        propagatedGibbsDensity H₀ h₀ β 0 :=
      (gibbsDensity_isHermitian
        (propagatedHamiltonian H₀ 0)
        (propagatedHamiltonian_isHermitian H₀ h₀ 0) β).star_eq
    have hconj : star (Matrix.trace
        (propagatedGibbsDensity H₀ h₀ β 0)) =
        Matrix.trace (propagatedGibbsDensity H₀ h₀ β 0) := by
      calc
        star (Matrix.trace (propagatedGibbsDensity H₀ h₀ β 0)) =
            Matrix.trace (star (propagatedGibbsDensity H₀ h₀ β 0)) := by
              rw [← Matrix.trace_conjTranspose]
              rfl
        _ = Matrix.trace (propagatedGibbsDensity H₀ h₀ β 0) :=
          congrArg Matrix.trace hDself
    exact Complex.conj_eq_iff_im.mp (by simpa [Complex.star_def] using hconj)
  have hscalar : (traceFunctional (δ : Carrier))⁻¹ = (z : ℂ)⁻¹ := by
    apply Complex.ext
    · simp [z, Complex.inv_re, Complex.normSq, him]
    · simp [z, Complex.inv_im, Complex.normSq, him]
  induction x using DirectLimit.induction with
  | _ n a =>
      have harg :
          star (⟦⟨n, a⟩⟧ : Carrier) * ⟦⟨n, a⟩⟧ =
            stageInjection n (star a * a) := by
        change star (stageInjection n a) * stageInjection n a =
          stageInjection n (star a * a)
        rw [← stageInjection_star, ← stageInjection_mul]
      rw [harg, normalizedDeltaWeightedFunctional_apply,
        deltaWeightedFunctional_apply, hscalar]
      rw [densityColimitUnit_coe_stage D hD
        (propagatedGibbsDensity_unit_zero H₀ h₀ β) n]
      rw [← stageInjection_mul, traceFunctional_stage]
      have hpos := propagatedGibbsDensity_stage_positive H₀ h₀ β n a
      have hz' : 0 < z⁻¹ := inv_pos.mpr hz
      have hzcomplex : ((z : ℂ)⁻¹).re = z⁻¹ := by
        simp [Complex.inv_re, Complex.normSq]
      have hzcomplex_im : ((z : ℂ)⁻¹).im = 0 := by
        simp [Complex.inv_im, Complex.normSq]
      rw [Complex.mul_re, hzcomplex, hzcomplex_im, zero_mul, sub_zero]
      exact mul_nonneg (le_of_lt hz') hpos

end InfoGeometry.Canonical.AlgebraicKMSStateColimit

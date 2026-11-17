/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.RealSpacetimeObserver
import InfoGeometry.Clifford.RightPhaseDynamics

/-!
# Right-phase mass signs on the native real spacetime algebra

The algebraic signs are unconditional. The field-operator conclusions assume
real linearity and compatibility with the specified constant right mass
coefficient. They do not construct a differential operator or assert PDE
well-posedness. A pseudoscalar formulation is equivalent to the bivector
formulation when the mass factor is transformed with it.
-/

noncomputable section

namespace InfoGeometry.Clifford.RealSpacetimeMassSigns

open HestenesCl14
open RealSpacetimeQuaternion RealSpacetimeSpinor RealSpacetimeObserver RightPhaseDynamics

theorem volume_sq : (volume : Cl14) * (volume : Cl14) = -1 := by
  apply quaternionRep_injective
  simp only [map_mul, quaternionRep_volume, map_neg, map_one]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem volume_anticommutes_gamma (i : Fin 4) :
    (volume : Cl14) * gamma i = -(gamma i * (volume : Cl14)) := by
  apply quaternionRep_injective
  simp only [map_mul, map_neg, quaternionRep_volume, quaternionRep_gamma]
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;> ext <;>
    norm_num [vectorMatrix, basisVec, Matrix.mul_apply, Fin.sum_univ_two]

theorem volume_commutes_even (x : ClPlus14) : volume * x = x * volume := by
  apply Subtype.ext
  apply quaternionRep_injective
  change quaternionRep ((volume : Cl14) * (x : Cl14)) =
    quaternionRep ((x : Cl14) * (volume : Cl14))
  rw [map_mul, map_mul, quaternionRep_volume, quaternionRep_even_shape x]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [evenMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem time_phase_sq :
    (gamma 0 * (phaseBivector : Cl14)) * (gamma 0 * (phaseBivector : Cl14)) = -1 := by
  apply quaternionRep_injective
  change quaternionRep ((gamma 0 * (gamma 2 * gamma 1)) *
    (gamma 0 * (gamma 2 * gamma 1))) = _
  simp only [map_mul, map_neg, map_one, quaternionRep_gamma]
  ext i j <;> fin_cases i <;> fin_cases j <;> ext <;>
    norm_num [vectorMatrix, basisVec, Matrix.mul_apply, Fin.sum_univ_two]

theorem time_volume_sq :
    (gamma 0 * (volume : Cl14)) * (gamma 0 * (volume : Cl14)) = 1 := by
  apply quaternionRep_injective
  simp only [map_mul, map_one, quaternionRep_volume, quaternionRep_gamma_zero]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [timeMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem spatial_volume_sq :
    (gamma 3 * (volume : Cl14)) * (gamma 3 * (volume : Cl14)) = -1 := by
  apply quaternionRep_injective
  simp only [map_mul, map_neg, map_one, quaternionRep_volume, quaternionRep_gamma]
  ext i j <;> fin_cases i <;> fin_cases j <;> ext <;>
    norm_num [vectorMatrix, basisVec, Matrix.mul_apply, Fin.sum_univ_two]

theorem phase_mul_sigma_three : (phaseBivector : Cl14) * sigma 2 = (volume : Cl14) := by
  apply quaternionRep_injective
  change quaternionRep ((gamma 2 * gamma 1) * (gamma 3 * gamma 0)) = _
  simp only [map_mul, quaternionRep_gamma, quaternionRep_volume]
  ext i j <;> fin_cases i <;> fin_cases j <;> ext <;>
    norm_num [vectorMatrix, basisVec, Matrix.mul_apply, Fin.sum_univ_two]

theorem volume_mul_sigma_three : (volume : Cl14) * sigma 2 = (phaseBivector : Cl14) := by
  apply quaternionRep_injective
  change quaternionRep ((volume : Cl14) * (gamma 3 * gamma 0)) =
    quaternionRep (gamma 2 * gamma 1)
  simp only [map_mul, quaternionRep_gamma, quaternionRep_volume]
  ext i j <;> fin_cases i <;> fin_cases j <;> ext <;>
    norm_num [vectorMatrix, basisVec, Matrix.mul_apply, Fin.sum_univ_two]

theorem time_mul_sigma_three : gamma 0 * sigma 2 = -gamma 3 := by
  apply quaternionRep_injective
  simp only [sigma, map_mul, map_neg, quaternionRep_gamma]
  ext i j <;> fin_cases i <;> fin_cases j <;> ext <;>
    norm_num [vectorMatrix, basisVec, Matrix.mul_apply, Fin.sum_univ_two]

theorem spatial_mul_sigma_three : gamma 3 * sigma 2 = -gamma 0 := by
  change gamma 3 * (gamma 3 * gamma 0) = -gamma 0
  rw [← mul_assoc, gamma_three_sq]
  simp

/-- Changing the phase requires changing the mass factor; both directions are proved. -/
theorem bivector_equation_iff_pseudoscalar (a ψ : Cl14) (m : ℝ) :
    a * (phaseBivector : Cl14) = m • (ψ * gamma 0) ↔
      a * (volume : Cl14) = (-m) • (ψ * gamma 3) := by
  constructor
  · intro h
    have ht := congrArg (fun z : Cl14 => z * sigma 2) h
    simpa only [mul_assoc, phase_mul_sigma_three, time_mul_sigma_three,
      smul_mul_assoc, mul_neg, smul_neg, neg_smul] using ht
  · intro h
    have ht := congrArg (fun z : Cl14 => z * sigma 2) h
    simpa only [mul_assoc, volume_mul_sigma_three, spatial_mul_sigma_three,
      smul_mul_assoc, mul_neg, smul_neg, neg_smul, neg_neg] using ht

section FieldOperator

variable {X : Type*}

/-- Conditional free-equation squaring with the actual right spin-plane phase. -/
theorem bivector_equation_second_iterate
    (D : (X → Cl14) →ₗ[ℝ] (X → Cl14)) (ψ : X → Cl14) (m : ℝ)
    (hright : ∀ f : X → Cl14,
      D (fun x => f x * (gamma 0 * (phaseBivector : Cl14))) =
        fun x => D f x * (gamma 0 * (phaseBivector : Cl14)))
    (hψ : (fun x => D ψ x * (phaseBivector : Cl14)) = fun x => m • (ψ x * gamma 0)) :
    D (D ψ) = fun x => (-(m ^ 2)) • ψ x := by
  have hb : (phaseBivector : Cl14) * (phaseBivector : Cl14) = -1 := by
    exact congrArg (fun x : ClPlus14 => (x : Cl14)) phaseBivector_sq
  have hfirst := (right_phase_equation_iff D ψ m (gamma 0) (phaseBivector : Cl14) hb).mp hψ
  have hs : (gamma 0 * (phaseBivector : Cl14)) * (gamma 0 * (phaseBivector : Cl14)) =
      (-1 : ℝ) • (1 : Cl14) := by simpa using time_phase_sq
  have h := second_iterate_of_right_mass_equation D ψ (-m) (-1)
    (gamma 0 * (phaseBivector : Cl14)) hs hright
    (by simpa only [mul_assoc] using hfirst)
  simpa using h

/-- The naive pseudoscalar replacement with the unchanged time mass factor has opposite sign. -/
theorem naive_pseudoscalar_second_iterate
    (D : (X → Cl14) →ₗ[ℝ] (X → Cl14)) (ψ : X → Cl14) (m : ℝ)
    (hright : ∀ f : X → Cl14,
      D (fun x => f x * (gamma 0 * (volume : Cl14))) =
        fun x => D f x * (gamma 0 * (volume : Cl14)))
    (hψ : (fun x => D ψ x * (volume : Cl14)) = fun x => m • (ψ x * gamma 0)) :
    D (D ψ) = fun x => (m ^ 2) • ψ x := by
  have hfirst := (right_phase_equation_iff D ψ m (gamma 0) (volume : Cl14) volume_sq).mp hψ
  have hs : (gamma 0 * (volume : Cl14)) * (gamma 0 * (volume : Cl14)) =
      (1 : ℝ) • (1 : Cl14) := by simpa using time_volume_sq
  have h := second_iterate_of_right_mass_equation D ψ (-m) 1
    (gamma 0 * (volume : Cl14)) hs hright
    (by simpa only [mul_assoc] using hfirst)
  simpa using h

/-- The correctly transformed pseudoscalar equation retains the negative mass square. -/
theorem transformed_pseudoscalar_second_iterate
    (D : (X → Cl14) →ₗ[ℝ] (X → Cl14)) (ψ : X → Cl14) (m : ℝ)
    (hright : ∀ f : X → Cl14,
      D (fun x => f x * (gamma 3 * (volume : Cl14))) =
        fun x => D f x * (gamma 3 * (volume : Cl14)))
    (hψ : (fun x => D ψ x * (volume : Cl14)) = fun x => (-m) • (ψ x * gamma 3)) :
    D (D ψ) = fun x => (-(m ^ 2)) • ψ x := by
  have hfirst := (right_phase_equation_iff D ψ (-m) (gamma 3) (volume : Cl14) volume_sq).mp hψ
  have hs : (gamma 3 * (volume : Cl14)) * (gamma 3 * (volume : Cl14)) =
      (-1 : ℝ) • (1 : Cl14) := by simpa using spatial_volume_sq
  have h := second_iterate_of_right_mass_equation D ψ m (-1)
    (gamma 3 * (volume : Cl14)) hs hright
    (by simpa only [neg_neg, mul_assoc] using hfirst)
  simpa using h

end FieldOperator

end InfoGeometry.Clifford.RealSpacetimeMassSigns

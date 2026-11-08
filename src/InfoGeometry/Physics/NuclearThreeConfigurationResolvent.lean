/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearThreeConfiguration
import InfoGeometry.Physics.NuclearRealKreinFeshbach
import Mathlib.Analysis.Analytic.Constructions

/-!
# Actual real resolvent of the three-configuration complementary corner

The native complementary block is `c • complement`, so its supported inverse
at a real energy away from `c` is explicit. The owned `graphMap` is exactly the
Feshbach wave map applied to the model inclusion. The two-coordinate effective
operator and its exact eigen equation are derived from those actual operators.

Real analyticity uses Mathlib's `AnalyticOnNhd ℝ`, and the open midpoint window
has an explicit distance from the complementary pole. These finite identities
do not identify physical configuration labels or introduce complex scalars.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearThreeConfigurationResolvent

open NuclearThreeConfiguration
open scoped Matrix

/-- The complementary inverse, supported on the actual eliminated coordinate. -/
def resolvent (c E : ℝ) : ConfigurationSpace →L[ℝ] ConfigurationSpace :=
  (E - c)⁻¹ • complement

@[simp] theorem resolvent_apply (c E : ℝ) (x : ConfigurationSpace) :
    resolvent c E x = WithLp.toLp 2 ![0, 0, x 2 / (E - c)] := by
  ext i
  fin_cases i <;> simp [resolvent, div_eq_mul_inv, mul_comm]

@[simp] theorem resolvent_at_pole (c : ℝ) : resolvent c c = 0 := by
  ext x i
  fin_cases i <;> simp

theorem complement_mul_resolvent (c E : ℝ) :
    complement * resolvent c E = resolvent c E := by
  ext x i
  fin_cases i <;> simp

theorem resolvent_mul_complement (c E : ℝ) :
    resolvent c E * complement = resolvent c E := by
  ext x i
  fin_cases i <;> simp

/-- The denominator is evaluated on the actual three-configuration operator. -/
theorem denominator_eq (a c g E : ℝ) :
    NuclearRealKreinFeshbach.denominator projection (hamiltonian a c g) E =
      (E - c) • complement := by
  change E • complement - complement * hamiltonian a c g * complement =
    (E - c) • complement
  rw [complement_hamiltonian_complement]
  ext x i
  fin_cases i <;> simp <;> ring

theorem denominator_mul_resolvent (a c g E : ℝ) (hE : E ≠ c) :
    NuclearRealKreinFeshbach.denominator projection (hamiltonian a c g) E *
        resolvent c E = complement := by
  have hEc : E - c ≠ 0 := sub_ne_zero.mpr hE
  rw [denominator_eq]
  ext x i
  fin_cases i <;> simp <;> field_simp [hEc] <;> ring

theorem resolvent_mul_denominator (a c g E : ℝ) (hE : E ≠ c) :
    resolvent c E *
        NuclearRealKreinFeshbach.denominator projection (hamiltonian a c g) E =
      complement := by
  have hEc : E - c ≠ 0 := sub_ne_zero.mpr hE
  rw [denominator_eq]
  ext x i
  fin_cases i <;> simp <;> field_simp [hEc] <;> ring

/-- The removed coordinate is a genuine nonzero operator corner. -/
theorem complement_ne_zero : complement ≠ 0 := by
  intro h
  have hx := congrArg
    (fun T : ConfigurationSpace →L[ℝ] ConfigurationSpace =>
      (T (WithLp.toLp 2 ![0, 0, (1 : ℝ)])) 2) h
  norm_num at hx

/-- The explicit inverse equations fail at the actual complementary pole. -/
theorem denominator_mul_resolvent_eq_complement_iff (a c g E : ℝ) :
    NuclearRealKreinFeshbach.denominator projection (hamiltonian a c g) E *
        resolvent c E = complement ↔ E ≠ c := by
  constructor
  · intro h hEc
    subst E
    rw [resolvent_at_pole, mul_zero] at h
    exact complement_ne_zero h.symm
  · exact denominator_mul_resolvent a c g E

/-- This is an equality of total real formulas. Its spectral interpretation
uses the separate inverse condition `E ≠ c`. -/
theorem graphMap_eq_waveOperator (a c g E : ℝ) :
    graphMap c g E =
      (NuclearRealKreinFeshbach.waveOperator projection
        (hamiltonian a c g) (resolvent c E)).comp inclusion := by
  ext x i
  fin_cases i <;>
    simp [NuclearRealKreinFeshbach.waveOperator, resolvent, div_eq_mul_inv] <;> ring

/-- Direct forward link to the original algebraic Feshbach owner. -/
theorem graphMap_toLinearMap_eq_waveOperator (a c g E : ℝ) :
    (graphMap c g E).toLinearMap =
      (NuclearFeshbachReduction.waveOperator projection.toLinearMap
        (hamiltonian a c g).toLinearMap (resolvent c E).toLinearMap).comp
          inclusion.toLinearMap := by
  exact congrArg ContinuousLinearMap.toLinearMap (graphMap_eq_waveOperator a c g E)

/-- The two retained coordinates with their exact energy-dependent correction. -/
def reducedHamiltonian (a c g E : ℝ) : ModelSpace →L[ℝ] ModelSpace :=
  matrixMap !![a + g ^ 2 / (E - c), g ^ 2 / (E - c);
    g ^ 2 / (E - c), a + g ^ 2 / (E - c)]

/-- The concrete effective matrix is evaluated from the full native operator. -/
theorem effectiveHamiltonian_inclusion (a c g E : ℝ) :
    (NuclearRealKreinFeshbach.effectiveHamiltonian projection
      (hamiltonian a c g) (resolvent c E)).comp inclusion =
        inclusion.comp (reducedHamiltonian a c g E) := by
  ext x i
  fin_cases i <;>
    simp [NuclearRealKreinFeshbach.effectiveHamiltonian, resolvent,
      reducedHamiltonian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      div_eq_mul_inv] <;> ring

theorem coordinates_effectiveHamiltonian_inclusion (a c g E : ℝ) :
    coordinates.comp
      ((NuclearRealKreinFeshbach.effectiveHamiltonian projection
        (hamiltonian a c g) (resolvent c E)).comp inclusion) =
      reducedHamiltonian a c g E := by
  rw [effectiveHamiltonian_inclusion, ← ContinuousLinearMap.comp_assoc,
    coordinates_inclusion, ContinuousLinearMap.id_comp]

theorem inclusion_injective : Function.Injective inclusion := by
  intro x y h
  have hx := congrArg (fun T : ModelSpace →L[ℝ] ModelSpace => T x)
    coordinates_inclusion
  have hy := congrArg (fun T : ModelSpace →L[ℝ] ModelSpace => T y)
    coordinates_inclusion
  exact hx.symm.trans ((congrArg coordinates h).trans hy)

/-- Exact spectral correspondence for the concrete graph and reduced matrix. -/
theorem graphMap_eigen_equation_iff (a c g E : ℝ) (hE : E ≠ c) (x : ModelSpace) :
    hamiltonian a c g (graphMap c g E x) = E • graphMap c g E x ↔
      reducedHamiltonian a c g E x = E • x := by
  have hmodel : projection (inclusion x) = inclusion x := by
    ext i
    fin_cases i <;> simp
  have h := NuclearRealKreinFeshbach.eigen_equation_iff projection
    (hamiltonian a c g) (resolvent c E) E
    (complement_mul_resolvent c E)
    (denominator_mul_resolvent a c g E hE) (inclusion x) hmodel
  have hw := congrArg (fun T : ModelSpace →L[ℝ] ConfigurationSpace => T x)
    (graphMap_eq_waveOperator a c g E)
  have heff := congrArg (fun T : ModelSpace →L[ℝ] ConfigurationSpace => T x)
    (effectiveHamiltonian_inclusion a c g E)
  change graphMap c g E x =
    NuclearRealKreinFeshbach.waveOperator projection
      (hamiltonian a c g) (resolvent c E) (inclusion x) at hw
  change NuclearRealKreinFeshbach.effectiveHamiltonian projection
      (hamiltonian a c g) (resolvent c E) (inclusion x) =
    inclusion (reducedHamiltonian a c g E x) at heff
  rw [← hw, heff] at h
  refine h.trans ?_
  constructor
  · intro he
    apply inclusion_injective
    simpa only [map_smul] using he
  · intro he
    rw [he, map_smul]

/-- An open real interval below the midpoint between the diagonal energies. -/
def validityWindow (a c : ℝ) : Set ℝ := Set.Iio ((a + c) / 2)

theorem energy_lt_eliminated (a c E : ℝ) (hac : a < c)
    (hE : E ∈ validityWindow a c) : E < c := by
  change E < (a + c) / 2 at hE
  linarith only [hac, hE]

theorem energy_ne_eliminated (a c E : ℝ) (hac : a < c)
    (hE : E ∈ validityWindow a c) : E ≠ c :=
  ne_of_lt (energy_lt_eliminated a c E hac hE)

/-- Genuine real analyticity of the operator-valued complementary resolvent. -/
theorem analyticOnNhd_resolvent (c : ℝ) :
    AnalyticOnNhd ℝ (resolvent c) {E : ℝ | E ≠ c} := by
  have hsub : AnalyticOnNhd ℝ (fun E : ℝ => E - c) {E : ℝ | E ≠ c} :=
    analyticOnNhd_id.sub analyticOnNhd_const
  have hinv : AnalyticOnNhd ℝ (fun E : ℝ => (E - c)⁻¹) {E : ℝ | E ≠ c} :=
    hsub.inv (fun E hE => sub_ne_zero.mpr hE)
  exact hinv.smul
    (analyticOnNhd_const : AnalyticOnNhd ℝ
      (fun _ : ℝ => complement) {E : ℝ | E ≠ c})

theorem analyticOnNhd_resolvent_validityWindow (a c : ℝ) (hac : a < c) :
    AnalyticOnNhd ℝ (resolvent c) (validityWindow a c) :=
  (analyticOnNhd_resolvent c).mono
    (fun E hE => energy_ne_eliminated a c E hac hE)

/-- Exact operator norm without assuming a previously unproved norm of `Q`. -/
theorem norm_resolvent (c E : ℝ) :
    ‖resolvent c E‖ = |E - c|⁻¹ * ‖complement‖ := by
  simp only [resolvent, norm_smul, norm_inv, Real.norm_eq_abs]

theorem norm_resolvent_le (c E δ : ℝ) (hδ : 0 < δ) (hgap : δ ≤ |E - c|) :
    ‖resolvent c E‖ ≤ δ⁻¹ * ‖complement‖ := by
  rw [norm_resolvent]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg complement)
  simpa only [one_div] using one_div_le_one_div_of_le hδ hgap

/-- The midpoint window has a uniform explicit distance from the pole. -/
theorem norm_resolvent_le_on_validityWindow (a c E : ℝ) (hac : a < c)
    (hE : E ∈ validityWindow a c) :
    ‖resolvent c E‖ ≤ ((c - a) / 2)⁻¹ * ‖complement‖ := by
  apply norm_resolvent_le c E ((c - a) / 2)
  · linarith
  · have hEc : E - c < 0 := sub_neg.mpr (energy_lt_eliminated a c E hac hE)
    rw [abs_of_neg hEc]
    change E < (a + c) / 2 at hE
    linarith

end InfoGeometry.Physics.NuclearThreeConfigurationResolvent

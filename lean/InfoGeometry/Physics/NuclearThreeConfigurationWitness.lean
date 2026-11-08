/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearThreeConfigurationInference

/-!
# Coupling-sign conjugacy and a nontrivial exact instance

The sign ambiguity of joint inference is implemented by an actual real
orthogonal change of the eliminated coordinate. The exact rational instance
has nonzero model/complement coupling; it is not an experimental fit.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearThreeConfigurationWitness

open scoped Matrix
open InfoGeometry.Physics.NuclearThreeConfiguration
open InfoGeometry.Physics.NuclearThreeConfigurationTransition

/-- The real basis change on the omitted configuration. -/
def signGauge : ConfigurationSpace →L[ℝ] ConfigurationSpace :=
  matrixMap !![1, 0, 0; 0, 1, 0; 0, 0, -1]

@[simp] theorem signGauge_apply (x : ConfigurationSpace) :
    signGauge x = WithLp.toLp 2 ![x 0, x 1, -x 2] := by
  ext i
  fin_cases i <;> simp [signGauge, dotProduct, Fin.sum_univ_succ]

theorem signGauge_adjoint : signGauge.adjoint = signGauge := by
  rw [signGauge, matrixMap_adjoint]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem signGauge_sq : signGauge * signGauge = 1 := by
  ext x i
  fin_cases i <;> simp

theorem signGauge_orthogonal : signGauge.adjoint * signGauge = 1 := by
  rw [signGauge_adjoint, signGauge_sq]

theorem signGauge_hamiltonian (a c g : ℝ) :
    signGauge * hamiltonian a c g * signGauge = hamiltonian a c (-g) := by
  ext x i
  fin_cases i <;> simp <;> ring

theorem signGauge_projection : signGauge * projection = projection := by
  ext x i
  fin_cases i <;> simp

theorem signGauge_probe (κ : ℝ) : signGauge * probe κ * signGauge = probe κ := by
  ext x i
  fin_cases i <;> simp

theorem signGauge_graphMap (c g E : ℝ) :
    signGauge.comp (graphMap c g E) = graphMap c (-g) E := by
  ext x i
  fin_cases i <;> simp <;> ring

theorem measuredStrength_sign_invariant (a c g E κ : ℝ) :
    measuredStrength a c (-g) E κ = measuredStrength a c g E κ := by
  rw [measuredStrength_eq_gram_ratio, measuredStrength_eq_gram_ratio]
  simp

/-- The rational witness meets the strict hypotheses used for inference. -/
theorem example_domain : (2 : ℝ) < 3 ∧ (1 : ℝ) ≠ 0 ∧
    (1 : ℝ) < (2 + 3) / 2 := by norm_num

theorem example_bright_eigen_equation :
    hamiltonian 2 3 1 (graphMap 3 1 1 brightModel) =
      (1 : ℝ) • graphMap 3 1 1 brightModel := by
  apply (bright_eigen_equation_iff 2 3 1 1 (by norm_num)).mpr
  norm_num

theorem example_strength : measuredStrength 2 3 1 1 1 = (2 : ℝ) / 3 := by
  rw [measuredStrength_closed_form 2 3 1 1 1 (by norm_num)]
  norm_num

/-- The resolvent correction is exercised by a genuinely coupled instance. -/
theorem example_coupling_nonzero :
    projection * hamiltonian 2 3 1 * complement ≠ 0 := by
  intro h
  have hx := congrArg
    (fun A : ConfigurationSpace →L[ℝ] ConfigurationSpace =>
      (A (WithLp.toLp 2 ![0, 0, (1 : ℝ)])) 0) h
  norm_num at hx

end InfoGeometry.Physics.NuclearThreeConfigurationWitness

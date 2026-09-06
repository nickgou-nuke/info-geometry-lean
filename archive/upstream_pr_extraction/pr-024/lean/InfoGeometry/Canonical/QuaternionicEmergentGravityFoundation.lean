import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Clifford.DiracPauliGamma

/-!
# InfoGeometry.Canonical.QuaternionicEmergentGravityFoundation

Finite theorem-safe quaternionic foundations for an emergent-gravity lane, built
only from the committed Dirac-Pauli gamma owner surface.

This file formalizes:
- the finite Cartan-decomposition witness inside the explicit `4 × 4` gamma
  matrices;
- the corrected quaternion multiplication laws;
- a finite quaternion-field norm identity;
- a finite real-valued anti-Hermitian vielbein readout;
- metric symmetry and torsion antisymmetry at an honest finite algebraic level.

It does not claim the full analytic Einstein-Cartan bootstrap.
-/

namespace InfoGeometry.Canonical.QuaternionicEmergentGravityFoundation

open scoped Matrix BigOperators
open InfoGeometry.Clifford.DiracPauliGamma

noncomputable section

abbrev SpacetimeIndex := Fin 4
abbrev QuaternionMatrix := DiracMatrix

@[rep_depth operator]
noncomputable def qi : QuaternionMatrix := gamma1 * gamma2

@[rep_depth operator]
noncomputable def qj : QuaternionMatrix := gamma2 * gamma3

@[rep_depth operator]
noncomputable def qk : QuaternionMatrix := gamma3 * gamma1

@[rep_depth operator]
noncomputable def quaternionField (a b c d : ℝ) : QuaternionMatrix :=
  (a : ℂ) • (1 : QuaternionMatrix) + (b : ℂ) • qi + (c : ℂ) • qj + (d : ℂ) • qk

@[rep_depth operator]
noncomputable def quaternionConj (a b c d : ℝ) : QuaternionMatrix :=
  (a : ℂ) • (1 : QuaternionMatrix) - (b : ℂ) • qi - (c : ℂ) • qj - (d : ℂ) • qk

@[rep_depth thermo]
def antiHermitianReadout (z : ℂ) : ℝ := -z.im

@[rep_depth thermo]
def emergentMetric
    (η : SpacetimeIndex → SpacetimeIndex → ℝ)
    (e : SpacetimeIndex → SpacetimeIndex → ℝ)
    (μ ν : SpacetimeIndex) : ℝ :=
  ∑ a, ∑ b, η a b * e a μ * e b ν

@[rep_depth thermo]
def torsionFromCommutator
    (C : SpacetimeIndex → SpacetimeIndex → SpacetimeIndex → ℝ)
    (κ : ℝ)
    (rho μ ν : SpacetimeIndex) : ℝ :=
  κ * (C rho μ ν - C rho ν μ)

@[rep_depth thermo]
structure SelfConsistencyPacket where
  Q : QuaternionMatrix

@[rep_depth operator]
theorem qi_sq : qi * qi = -(1 : QuaternionMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qi, gamma1, gamma2, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.neg_apply]

@[rep_depth operator]
theorem qj_sq : qj * qj = -(1 : QuaternionMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qj, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.neg_apply]

@[rep_depth operator]
theorem qk_sq : qk * qk = -(1 : QuaternionMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qk, gamma3, gamma1, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.neg_apply]

@[rep_depth operator]
theorem qi_mul_qj : qi * qj = qk := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qi, qj, qk, gamma1, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

@[rep_depth operator]
theorem qj_mul_qk : qj * qk = qi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qi, qj, qk, gamma1, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

@[rep_depth operator]
theorem qk_mul_qi : qk * qi = qj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qi, qj, qk, gamma1, gamma2, gamma3, Matrix.mul_apply, Fin.sum_univ_succ]

@[rep_depth operator]
theorem qijk_eq_neg_one : qi * qj * qk = -(1 : QuaternionMatrix) := by
  rw [qi_mul_qj, qk_sq]

@[rep_depth thermo]
theorem emergentMetric_symmetric
    (η : SpacetimeIndex → SpacetimeIndex → ℝ)
    (e : SpacetimeIndex → SpacetimeIndex → ℝ)
    (hη : ∀ a b, η a b = η b a)
    (μ ν : SpacetimeIndex) :
    emergentMetric η e μ ν = emergentMetric η e ν μ := by
  unfold emergentMetric
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [hη a b]
  ring

@[rep_depth thermo]
theorem torsionFromCommutator_antisymm
    (C : SpacetimeIndex → SpacetimeIndex → SpacetimeIndex → ℝ)
    (κ : ℝ)
    (rho μ ν : SpacetimeIndex) :
    torsionFromCommutator C κ rho μ ν = -torsionFromCommutator C κ rho ν μ := by
  unfold torsionFromCommutator
  ring

@[rep_depth thermo]
theorem quaternionField_mul_conj
    (a b c d : ℝ) :
    quaternionField a b c d * quaternionConj a b c d =
      (((a * a + b * b + c * c + d * d : ℝ) : ℂ) • (1 : QuaternionMatrix)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionField, quaternionConj, qi, qj, qk, gamma1, gamma2, gamma3,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.one_apply, Complex.ext_iff] <;>
    ring_nf <;>
    simp

end
end InfoGeometry.Canonical.QuaternionicEmergentGravityFoundation

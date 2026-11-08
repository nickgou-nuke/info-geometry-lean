/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AttentionLogPartitionModularBridge
import InfoGeometry.QuantumContext.CarrierInnerModularBoundary
import InfoGeometry.Canonical.FiniteFisherRaoSquareRoot

/-!
# Thermal log-partition identities on the attention matrix carrier

This module connects the finite energy convention to the existing complex
modular action on the algebraic matrix direct-limit carrier. It also realizes
the corresponding finite softmax distribution in the repository's
Fisher--Rao square-root owner. The statements are algebraic and finite-stage
based; they do not assert holomorphic continuation or a completed KMS strip.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.AttentionThermalColimitBridge

open BigOperators
open InfoGeometry.Canonical.FiniteFisherRaoSquareRoot
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.AttentionLogPartitionModularBridge
open InfoGeometry.QuantumContext.CarrierInnerModularBoundary

private theorem complexModularExponential_add_const (k : ℕ)
    (H : Fin (2 ^ k) → ℝ) (c β : ℝ) (z : ℂ) :
    complexModularExponential k (fun i => H i + c) β z =
      Complex.exp (Complex.I * z * (β : ℂ) * (c : ℂ)) •
        complexModularExponential k H β z := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [complexModularExponential, Matrix.diagonal_apply,
      complexModularPhase, Matrix.smul_apply, smul_eq_mul, ite_true]
    rw [show Complex.I * z * (β : ℂ) * ((H i + c : ℝ) : ℂ) =
        Complex.I * z * (β : ℂ) * (H i : ℂ) +
          Complex.I * z * (β : ℂ) * (c : ℂ) by push_cast; ring,
      Complex.exp_add]
    ring
  · simp [complexModularExponential, hij]

private theorem scalar_left_right_cancel {A : Type*} [Ring A] [Algebra ℂ A]
    (c d : ℂ) (hcd : c * d = 1) (a y b : A) :
    (c • a) * y * (d • b) = a * y * b := by
  calc
    (c • a) * y * (d • b) = c • (a * y * (d • b)) := by
      rw [smul_mul_assoc, smul_mul_assoc]
    _ = c • (d • (a * y * b)) := by
      congr 1
      rw [mul_smul_comm]
    _ = (c * d) • (a * y * b) := by rw [smul_smul]
    _ = a * y * b := by rw [hcd, one_smul]

private theorem complex_shift_scalars_cancel (c β : ℝ) (z : ℂ) :
    Complex.exp (Complex.I * z * (β : ℂ) * (c : ℂ)) *
      Complex.exp (Complex.I * (-z) * (β : ℂ) * (c : ℂ)) = 1 := by
  rw [← Complex.exp_add]
  rw [show Complex.I * z * (β : ℂ) * (c : ℂ) +
      Complex.I * (-z) * (β : ℂ) * (c : ℂ) = 0 by ring,
    Complex.exp_zero]

/-- A common real shift of the diagonal generator cancels from the complex
inner-conjugation action on every element of the full algebraic matrix
direct-limit carrier. -/
theorem carrierComplexModularFlow_add_const (k : ℕ)
    (H : Fin (2 ^ k) → ℝ) (c β : ℝ) (z : ℂ) (x : Carrier) :
    carrierComplexModularFlow k (fun i => H i + c) β z x =
      carrierComplexModularFlow k H β z x := by
  unfold carrierComplexModularFlow
  rw [complexModularExponential_add_const,
    complexModularExponential_add_const]
  rw [map_smul, map_smul]
  exact scalar_left_right_cancel _ _
    (complex_shift_scalars_cancel c β z) _ _ _

/-- For the Gibbs convention `rho_i = exp(-β E_i)/Z`, the scalar log-partition
term in `log rho = -K` cancels from the full-carrier complex modular action.
The result is an identity for the algebraically defined complex parameter
action at every `z : ℂ`, without claiming analytic continuation. -/
theorem thermalCarrierFlow_eq_centeredEnergyFlow (k : ℕ)
    (energy : Fin (2 ^ k) → ℝ) (β : ℝ) (z : ℂ) (x : Carrier) :
    carrierComplexModularFlow k
        (fun i => -modularHamiltonian energy β i) 1 z x =
      carrierComplexModularFlow k (fun i => -(β * energy i)) 1 z x := by
  have hshift :
      (fun i => -modularHamiltonian energy β i) =
        (fun i => -(β * energy i) + -(logPartitionPotential energy β)) := by
    funext i
    simp [modularHamiltonian]
    ring
  rw [hshift]
  exact carrierComplexModularFlow_add_const k
    (fun i => -(β * energy i)) (-(logPartitionPotential energy β)) 1 z x

/-- The positive finite energy softmax, packaged in the existing strictly
positive probability carrier. -/
def thermalProbability {ι : Type*} [Fintype ι] [Nonempty ι]
    (energy : ι → ℝ) (β : ℝ) : StrictProbability ι where
  probability := thermalWeight energy β
  probability_pos := by
    intro i
    simpa [thermalWeight] using
      softmaxWeight_pos (fun j => -energy j) β i
  sum_probability := by
    simpa [thermalWeight] using
      softmaxWeight_sum_one (fun j => -energy j) β

/-- The square-root amplitudes of the thermal attention state have unit
Euclidean norm. -/
theorem thermalSqrtAmplitude_normSq {ι : Type*} [Fintype ι] [Nonempty ι]
    (energy : ι → ℝ) (β : ℝ) :
    ∑ i : ι, (Real.sqrt (thermalWeight energy β i)) ^ 2 = 1 := by
  exact (thermalProbability energy β).sqrtAmplitude_normSq

/-- The thermal square-root amplitude includes both the energy contribution
and the common log-partition normalization. -/
theorem thermalWeight_sqrt_eq_exp_half_modularHamiltonian
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (energy : ι → ℝ) (β : ℝ) (i : ι) :
    Real.sqrt (thermalWeight energy β i) =
      Real.exp (-modularHamiltonian energy β i / 2) := by
  rw [thermalWeight_eq_exp_neg_modularHamiltonian]
  exact (Real.exp_half (-modularHamiltonian energy β i)).symm

end InfoGeometry.QuantumContext.AttentionThermalColimitBridge

end noncomputable section

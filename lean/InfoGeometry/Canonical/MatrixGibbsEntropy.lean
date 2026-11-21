/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteMatrixGibbsFunctional
import InfoGeometry.Canonical.MatrixEntropyUnitaryOrbit

/-!
# Actual matrix Gibbs logarithms and thermal entropy accounting

The Gibbs weight is the existing Hermitian functional-calculus construction.
Its normalized state uses the existing trace-density normalization on the full
complex matrix algebra. The actual CFC logarithm, rather than a supplied
logarithm variable, gives the thermal relative-log trace and free-energy
identities. No commutation between the comparison matrix and the Hamiltonian
is assumed.

The identities below are algebraic in the comparison matrix once its trace is
one. Their interpretation as entropy identities uses a positive density
matrix. Positivity of quantum relative entropy, bipartite entropy inequalities,
and a joint system-reservoir evolution are separate obligations.
-/

noncomputable section

namespace InfoGeometry.Canonical.MatrixGibbsEntropy

open FiniteMatrixGibbsFunctional PolarFrameTraceDensity MatrixEntropyUnitaryOrbit
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

local notation "Mat" => Matrix n n ℂ

/-- The real partition readout of the existing matrix Gibbs weight. -/
def gibbsPartition (H : Mat) (hH : H.IsHermitian) (β : ℝ) : ℝ :=
  traceMass (gibbsDensity H hH β)

/-- The normalized Gibbs state on the original full matrix carrier. -/
def normalizedGibbsDensity (H : Mat) (hH : H.IsHermitian) (β : ℝ) : Mat :=
  normalizedDensity (gibbsDensity H hH β)

/-- The Hermitian CFC Gibbs weight is the actual matrix exponential. -/
theorem gibbsDensity_eq_exp_neg_smul (H : Mat) (hH : H.IsHermitian) (β : ℝ) :
    gibbsDensity H hH β = NormedSpace.exp ((-β) • H) := by
  have hscaled : IsSelfAdjoint ((-β) • H) := (IsSelfAdjoint.all (-β)).smul hH
  calc
    gibbsDensity H hH β = cfc (expWeight β) H := (hH.cfc_eq _).symm
    _ = cfc Real.exp ((-β) • H) :=
      cfc_comp_smul (R := ℝ) (-β) Real.exp H (by fun_prop) hH
    _ = NormedSpace.exp ((-β) • H) := CFC.real_exp_eq_normedSpace_exp hscaled

/-- The operator logarithm inverts the actual Gibbs exponential. -/
theorem log_gibbsDensity (H : Mat) (hH : H.IsHermitian) (β : ℝ) :
    CFC.log (gibbsDensity H hH β) = (-β) • H := by
  rw [gibbsDensity_eq_exp_neg_smul]
  exact CFC.log_exp _ ((IsSelfAdjoint.all (-β)).smul hH)

variable [Nonempty n]

theorem gibbsPartition_pos (H : Mat) (hH : H.IsHermitian) (β : ℝ) :
    0 < gibbsPartition H hH β :=
  traceMass_pos _ (gibbsDensity_strictlyPositive H hH β)

theorem normalizedGibbsDensity_isStrictlyPositive
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) :
    IsStrictlyPositive (normalizedGibbsDensity H hH β) :=
  normalizedDensity_isStrictlyPositive _ (gibbsDensity_strictlyPositive H hH β)

theorem trace_normalizedGibbsDensity (H : Mat) (hH : H.IsHermitian) (β : ℝ) :
    Matrix.trace (normalizedGibbsDensity H hH β) = 1 :=
  trace_normalizedDensity _ (gibbsDensity_strictlyPositive H hH β)

theorem normalizedGibbsDensity_eq_normalized_exp
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) :
    normalizedGibbsDensity H hH β =
      (gibbsPartition H hH β)⁻¹ • NormedSpace.exp ((-β) • H) := by
  change (gibbsPartition H hH β)⁻¹ • gibbsDensity H hH β = _
  rw [gibbsDensity_eq_exp_neg_smul]

/-- Trace normalization produces the central logarithmic partition correction. -/
theorem log_normalizedGibbsDensity
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) :
    CFC.log (normalizedGibbsDensity H hH β) =
      (-β) • H - Real.log (gibbsPartition H hH β) • (1 : Mat) := by
  have h := neg_log_normalizedDensity (gibbsDensity H hH β)
    (gibbsDensity_strictlyPositive H hH β)
  change -CFC.log (normalizedGibbsDensity H hH β) =
    -CFC.log (gibbsDensity H hH β) +
      Real.log (gibbsPartition H hH β) • (1 : Mat) at h
  rw [log_gibbsDensity] at h
  have hneg := congrArg Neg.neg h
  convert hneg using 1 <;> simp only [neg_neg, neg_add, sub_eq_add_neg, neg_smul]

/-- The existing thermal modular expression is now an actual CFC logarithm. -/
theorem log_normalizedGibbsDensity_eq_thermalModularHamiltonian
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) :
    CFC.log (normalizedGibbsDensity H hH β) =
      QuantumRelativeSurprisal.thermalModularHamiltonian
        (β : ℂ) (Real.log (gibbsPartition H hH β) : ℂ) H := by
  rw [log_normalizedGibbsDensity]
  simp only [QuantumRelativeSurprisal.thermalModularHamiltonian,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have hβ : ((-β : ℝ) : ℂ) = -(β : ℂ) := by norm_num
  have hmul : ((-β : ℝ) : ℂ) • H = (-(β : ℂ)) • H :=
    congrArg (fun z : ℂ => z • H) hβ
  exact congrArg (fun z : Mat => z -
    (Real.log (gibbsPartition H hH β) : ℂ) • (1 : Mat)) hmul

/-- Thermal relative-log trace for an arbitrary trace-one comparison matrix. -/
theorem relativeLogTrace_eq_energy_sub_entropy
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) (ρ : Mat)
    (hρ : Matrix.trace ρ = 1) :
    (Matrix.trace (ρ * (CFC.log ρ -
      CFC.log (normalizedGibbsDensity H hH β)))).re =
      -matrixEntropy ρ + β * (Matrix.trace (ρ * H)).re +
        Real.log (gibbsPartition H hH β) := by
  have hthermal :
      (Matrix.trace (ρ * ((-β) • H -
        Real.log (gibbsPartition H hH β) • (1 : Mat)))).re =
        -β * (Matrix.trace (ρ * H)).re -
          Real.log (gibbsPartition H hH β) := by
    rw [mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.trace_smul, Matrix.trace_smul, mul_one, hρ]
    simp
  rw [log_normalizedGibbsDensity, mul_sub, Matrix.trace_sub,
    Complex.sub_re, hthermal, matrixEntropy_eq]
  ring

/-- Entropy of the actual normalized Gibbs density. -/
theorem matrixEntropy_normalizedGibbsDensity
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) :
    matrixEntropy (normalizedGibbsDensity H hH β) =
      β * (Matrix.trace (normalizedGibbsDensity H hH β * H)).re +
        Real.log (gibbsPartition H hH β) := by
  have h := relativeLogTrace_eq_energy_sub_entropy H hH β
    (normalizedGibbsDensity H hH β) (trace_normalizedGibbsDensity H hH β)
  simp only [sub_self, mul_zero, Matrix.trace_zero, Complex.zero_re] at h
  linarith

/-- The existing complex free-energy identity instantiated with actual logs. -/
theorem relativeLogTrace_eq_beta_freeEnergy_partition
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) (hβ : β ≠ 0)
    (ρ : Mat) (hρ : Matrix.trace ρ = 1) :
    Matrix.trace (ρ * (CFC.log ρ -
      CFC.log (normalizedGibbsDensity H hH β))) =
      (β : ℂ) *
        (QuantumRelativeSurprisal.freeEnergy (β : ℂ) H ρ (CFC.log ρ) -
          (-(Real.log (gibbsPartition H hH β) : ℂ) / (β : ℂ))) := by
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have h := QuantumRelativeSurprisal.relativeSurprisal_eq_beta_freeEnergy_diff
    (β : ℂ) (Real.log (gibbsPartition H hH β) : ℂ) hβc H ρ (CFC.log ρ) hρ
  rw [← log_normalizedGibbsDensity_eq_thermalModularHamiltonian H hH β] at h
  exact h

/-- The reference free energy is computed from the actual normalized state. -/
theorem freeEnergy_normalizedGibbsDensity
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) (hβ : β ≠ 0) :
    QuantumRelativeSurprisal.freeEnergy (β : ℂ) H
      (normalizedGibbsDensity H hH β) (CFC.log (normalizedGibbsDensity H hH β)) =
      -(Real.log (gibbsPartition H hH β) : ℂ) / (β : ℂ) := by
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  have h := relativeLogTrace_eq_beta_freeEnergy_partition H hH β hβ
    (normalizedGibbsDensity H hH β) (trace_normalizedGibbsDensity H hH β)
  simp only [sub_self, mul_zero, Matrix.trace_zero] at h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left hβc)

/-- Relative-log trace equals the actual Gibbs-referenced free-energy gap. -/
theorem relativeLogTrace_eq_beta_freeEnergy_diff
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) (hβ : β ≠ 0)
    (ρ : Mat) (hρ : Matrix.trace ρ = 1) :
    Matrix.trace (ρ * (CFC.log ρ -
      CFC.log (normalizedGibbsDensity H hH β))) =
      (β : ℂ) *
        (QuantumRelativeSurprisal.freeEnergy (β : ℂ) H ρ (CFC.log ρ) -
          QuantumRelativeSurprisal.freeEnergy (β : ℂ) H
            (normalizedGibbsDensity H hH β)
            (CFC.log (normalizedGibbsDensity H hH β))) := by
  rw [freeEnergy_normalizedGibbsDensity H hH β hβ]
  exact relativeLogTrace_eq_beta_freeEnergy_partition H hH β hβ ρ hρ

/-- Exact same-Hamiltonian energy accounting relative to a Gibbs reference.
The left side is inverse temperature times the bath's energy increase when
`ρ` is its final state; this theorem itself does not construct that evolution. -/
theorem gibbs_energy_entropy_balance
    (H : Mat) (hH : H.IsHermitian) (β : ℝ) (ρ : Mat)
    (hρ : Matrix.trace ρ = 1) :
    β * ((Matrix.trace (ρ * H)).re -
      (Matrix.trace (normalizedGibbsDensity H hH β * H)).re) =
      matrixEntropy ρ - matrixEntropy (normalizedGibbsDensity H hH β) +
        (Matrix.trace (ρ * (CFC.log ρ -
          CFC.log (normalizedGibbsDensity H hH β)))).re := by
  rw [matrixEntropy_normalizedGibbsDensity,
    relativeLogTrace_eq_energy_sub_entropy H hH β ρ hρ]
  ring

end InfoGeometry.Canonical.MatrixGibbsEntropy

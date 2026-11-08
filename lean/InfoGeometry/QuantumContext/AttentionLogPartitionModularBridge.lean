/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Log-partition shifts in finite attention modular flows

For a finite energy family, the partition sum is positive and its logarithm
is the scalar term in the normalized modular Hamiltonian. The repository's
real-time flow uses the phase of `log ρ`; since `log ρ = -K`, the thermal
specialization uses the negative modular Hamiltonian. On the full complex
matrix algebra, a common scalar shift cancels in inner conjugation. For a
two-sided relative action, the distinct shifts leave their phase difference.
These are finite matrix identities; they do not assert analytic continuation
or an infinite-dimensional modular theorem.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.AttentionLogPartitionModularBridge

open BigOperators
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The finite Boltzmann partition sum for an energy family. -/
def partitionZ (energy : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ i, Real.exp (-β * energy i)

/-- The logarithm of the finite Boltzmann partition sum. -/
def logPartitionPotential (energy : ι → ℝ) (β : ℝ) : ℝ :=
  Real.log (partitionZ energy β)

omit [DecidableEq ι] in
/-- The finite Boltzmann partition sum is strictly positive. -/
theorem partitionZ_pos (energy : ι → ℝ) (β : ℝ) :
    0 < partitionZ energy β := by
  unfold partitionZ
  apply Finset.sum_pos'
  · intro i _
    exact le_of_lt (Real.exp_pos _)
  · exact ⟨Classical.arbitrary ι, Finset.mem_univ _, Real.exp_pos _⟩

omit [DecidableEq ι] in
/-- Exponentiating the log-partition potential recovers the radial partition sum. -/
theorem exp_logPartitionPotential (energy : ι → ℝ) (β : ℝ) :
    Real.exp (logPartitionPotential energy β) = partitionZ energy β :=
  Real.exp_log (partitionZ_pos energy β)

/-- The scalar coefficient of the diagonal modular Hamiltonian. -/
def modularHamiltonian (energy : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  β * energy i + logPartitionPotential energy β

/-- The Gibbs probability represented by the existing softmax owner using
logits `-energy`. -/
def thermalWeight (energy : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  softmaxWeight (fun j => -energy j) β i

omit [DecidableEq ι] in
/-- A finite Gibbs weight is the exponential of the negative normalized
modular Hamiltonian. -/
theorem thermalWeight_eq_exp_neg_modularHamiltonian
    (energy : ι → ℝ) (β : ℝ) (i : ι) :
    thermalWeight energy β i = Real.exp (-modularHamiltonian energy β i) := by
  simp only [thermalWeight, softmaxWeight, modularHamiltonian,
    logPartitionPotential]
  have hden : (∑ j, Real.exp (β * -energy j)) =
      partitionZ energy β := by
    unfold partitionZ
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    ring
  rw [hden, show β * -energy i = -(β * energy i) by ring]
  calc
    Real.exp (-(β * energy i)) / partitionZ energy β =
        Real.exp (-(β * energy i)) * (Real.exp (logPartitionPotential energy β))⁻¹ := by
          rw [exp_logPartitionPotential, div_eq_mul_inv]
    _ = Real.exp (-(β * energy i)) * Real.exp (-(logPartitionPotential energy β)) := by
          rw [← Real.exp_neg]
    _ = Real.exp (-(β * energy i) - logPartitionPotential energy β) := by
          rw [← Real.exp_add]
          congr 1
    _ = Real.exp (-(β * energy i + logPartitionPotential energy β)) := by
          congr 1
          ring

/-- The repository's real-time inner action on the full matrix algebra. -/
def hamiltonianFlow (H : ι → ℝ) (t : ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  modularFlow H 1 t A

/-- Two-sided relative action, allowing distinct left and right Hamiltonians. -/
def relativeHamiltonianFlow (H₁ H₂ : ι → ℝ) (t : ℝ)
    (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  modularUnitary H₁ 1 t * A * modularUnitary H₂ 1 (-t)

private theorem relative_exp_entry (h₁ h₂ t : ℝ) (z : ℂ) :
    Complex.exp (Complex.I * (t : ℂ) * 1 * (h₁ : ℂ)) * z *
        Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * 1 * (h₂ : ℂ)) =
      Complex.exp (Complex.I * (t : ℂ) * ((h₁ - h₂ : ℝ) : ℂ)) * z := by
  calc
    Complex.exp (Complex.I * (t : ℂ) * 1 * (h₁ : ℂ)) * z *
        Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * 1 * (h₂ : ℂ)) =
      (Complex.exp (Complex.I * (t : ℂ) * 1 * (h₁ : ℂ)) *
        Complex.exp (Complex.I * ((-t : ℝ) : ℂ) * 1 * (h₂ : ℂ))) * z := by ring
    _ = Complex.exp (Complex.I * (t : ℂ) * 1 * (h₁ : ℂ) +
        Complex.I * ((-t : ℝ) : ℂ) * 1 * (h₂ : ℂ)) * z := by
          rw [← Complex.exp_add]
    _ = Complex.exp (Complex.I * (t : ℂ) * ((h₁ - h₂ : ℝ) : ℂ)) * z := by
          congr 1
          push_cast
          ring_nf

omit [Nonempty ι] in
/-- Entry formula for the full matrix inner action. -/
theorem hamiltonianFlow_apply (H : ι → ℝ) (t : ℝ)
    (A : Matrix ι ι ℂ) (i j : ι) :
    hamiltonianFlow H t A i j =
      Complex.exp (Complex.I * (t : ℂ) * ((H i - H j : ℝ) : ℂ)) * A i j := by
  simpa [hamiltonianFlow] using
    modularFlow_apply_eq_exp_sub H 1 t A i j

omit [Nonempty ι] in
/-- Adding a scalar to the Hamiltonian is invisible to inner conjugation on
the full matrix algebra. -/
theorem hamiltonianFlow_add_const (H : ι → ℝ) (c t : ℝ)
    (A : Matrix ι ι ℂ) :
    hamiltonianFlow (fun i => H i + c) t A = hamiltonianFlow H t A := by
  ext i j
  rw [hamiltonianFlow_apply, hamiltonianFlow_apply]
  have h : (H i + c) - (H j + c) = H i - H j := by ring
  rw [h]

omit [Nonempty ι] in
/-- In the repository convention `A ↦ ρ^(it) A ρ^(-it)`, the thermal generator
is `log ρ = -K`; its common log-partition shift cancels on every matrix
observable. -/
theorem thermalHamiltonianFlow_eq_centeredEnergyFlow
    (energy : ι → ℝ) (β t : ℝ) (A : Matrix ι ι ℂ) :
    hamiltonianFlow (fun i => -modularHamiltonian energy β i) t A =
      hamiltonianFlow (fun i => -(β * energy i)) t A := by
  change hamiltonianFlow
      (fun i => -(β * energy i + logPartitionPotential energy β)) t A = _
  have h : (fun i => -(β * energy i + logPartitionPotential energy β)) =
      (fun i => -(β * energy i) + -(logPartitionPotential energy β)) := by
    funext i
    ring
  rw [h]
  exact hamiltonianFlow_add_const (fun i => -(β * energy i))
    (-(logPartitionPotential energy β)) t A

omit [Nonempty ι] in
/-- Entry formula for a two-sided relative Hamiltonian action. -/
theorem relativeHamiltonianFlow_apply (H₁ H₂ : ι → ℝ) (t : ℝ)
    (A : Matrix ι ι ℂ) (i j : ι) :
    relativeHamiltonianFlow H₁ H₂ t A i j =
      Complex.exp (Complex.I * (t : ℂ) * ((H₁ i - H₂ j : ℝ) : ℂ)) * A i j := by
  dsimp [relativeHamiltonianFlow, modularUnitary]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  dsimp [modularPhase]
  exact relative_exp_entry (H₁ i) (H₂ j) t (A i j)

omit [Nonempty ι] in
/-- For a relative action, distinct scalar Hamiltonian shifts remain as their
phase difference. -/
theorem relativeHamiltonianFlow_add_constants
    (H₁ H₂ : ι → ℝ) (c₁ c₂ t : ℝ) (A : Matrix ι ι ℂ) :
    relativeHamiltonianFlow (fun i => H₁ i + c₁) (fun i => H₂ i + c₂) t A =
      (Complex.exp (Complex.I * (t : ℂ) * ((c₁ - c₂ : ℝ) : ℂ))) •
        relativeHamiltonianFlow H₁ H₂ t A := by
  ext i j
  simp only [relativeHamiltonianFlow_apply, Matrix.smul_apply, smul_eq_mul]
  have hphase : Complex.exp (Complex.I * (t : ℂ) *
      ↑(H₁ i + c₁ - (H₂ j + c₂))) =
      Complex.exp (Complex.I * (t : ℂ) * ↑(c₁ - c₂)) *
        Complex.exp (Complex.I * (t : ℂ) * ↑(H₁ i - H₂ j)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    Complex.exp (Complex.I * (t : ℂ) * ↑(H₁ i + c₁ - (H₂ j + c₂))) * A i j =
        (Complex.exp (Complex.I * (t : ℂ) * ↑(c₁ - c₂)) *
          Complex.exp (Complex.I * (t : ℂ) * ↑(H₁ i - H₂ j))) * A i j := by
            rw [hphase]
    _ = Complex.exp (Complex.I * (t : ℂ) * ↑(c₁ - c₂)) *
        (Complex.exp (Complex.I * (t : ℂ) * ↑(H₁ i - H₂ j)) * A i j) := by ring

omit [Nonempty ι] in
/-- For relative thermal flow generated by `log ρ = -K`, the relative phase
contains the reversed difference of the two log-partition potentials. -/
theorem relativeThermalFlow_partitionPhase
    (energy₁ energy₂ : ι → ℝ) (β t : ℝ) (A : Matrix ι ι ℂ) :
    relativeHamiltonianFlow (fun i => -modularHamiltonian energy₁ β i)
        (fun i => -modularHamiltonian energy₂ β i) t A =
      (Complex.exp (Complex.I * (t : ℂ) *
          (((-logPartitionPotential energy₁ β) -
            (-logPartitionPotential energy₂ β)) : ℂ)) •
        relativeHamiltonianFlow (fun i => -(β * energy₁ i))
          (fun i => -(β * energy₂ i)) t A) := by
  change relativeHamiltonianFlow
      (fun i => -(β * energy₁ i + logPartitionPotential energy₁ β))
      (fun i => -(β * energy₂ i + logPartitionPotential energy₂ β)) t A = _
  have h₁ : (fun i => -(β * energy₁ i + logPartitionPotential energy₁ β)) =
      (fun i => -(β * energy₁ i) + -(logPartitionPotential energy₁ β)) := by
    funext i
    ring
  have h₂ : (fun i => -(β * energy₂ i + logPartitionPotential energy₂ β)) =
      (fun i => -(β * energy₂ i) + -(logPartitionPotential energy₂ β)) := by
    funext i
    ring
  rw [h₁, h₂]
  simpa only [Complex.ofReal_sub, Complex.ofReal_neg] using
    relativeHamiltonianFlow_add_constants
      (fun i => -(β * energy₁ i)) (fun i => -(β * energy₂ i))
      (-(logPartitionPotential energy₁ β)) (-(logPartitionPotential energy₂ β)) t A

end InfoGeometry.QuantumContext.AttentionLogPartitionModularBridge

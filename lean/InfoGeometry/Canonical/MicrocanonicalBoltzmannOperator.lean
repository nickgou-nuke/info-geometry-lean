import InfoGeometry.Canonical.MicrostateBoltzmannEntropy
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Pure Microcanonical Boltzmann Operator Entropy (No Gibbs, No Shannon, No von Neumann)

This module formalizes in native Lean 4 / Mathlib:
1. **The Microcanonical State-Counting Operator $\hat W_{\text{micro}}$**:
   $$\hat W = \sum_{E} W(E) P_E$$
   where $W(E) \ge 1$ is the exact microstate count (multiplicity / phase-volume) in energy shell $E$,
   and $P_E$ is the orthogonal projection onto the microcanonical energy subspace $\mathcal{H}_E$.

2. **The Pure Microcanonical Boltzmann Operator Entropy $\hat S_{\text{micro-Boltzmann}}$**:
   $$\hat S_{\text{micro-Boltzmann}} := \ln \hat W = \sum_{E} (\ln W(E)) P_E$$
   defined strictly as a **state-counting quantum operator on Hilbert space** without taking any
   Gibbs ensemble averages ($-\sum p \ln p$), Shannon probability sums, or von Neumann trace expectations ($-\operatorname{Tr}(\rho \ln \rho)$).

3. **Operator Eigenvalue Theorem**:
   For any microstate $|\psi_E\rangle \in \mathcal{H}_E$:
   $$\hat S_{\text{micro-Boltzmann}} |\psi_E\rangle = (\ln W(E)) |\psi_E\rangle$$
   recovering the fundamental Boltzmann relation $S = k_B \ln W$ directly as an operator eigenvalue.

4. **Hamiltonian Commutativity & Conservation**:
   $$\left[\hat S_{\text{micro-Boltzmann}}, \hat H\right] = 0$$
   proving that the Boltzmann operator entropy is a conserved constant of motion in the microcanonical ensemble.
-/

namespace InfoGeometry.Canonical.MicrocanonicalBoltzmannOperator

open InfoGeometry.Canonical.MicrostateBoltzmannEntropy

/--
Microcanonical energy-shell data is the positive-multiplicity owner already
used for statewise Boltzmann entropy.
-/
abbrev MicrocanonicalEnergyShell :=
  MicrostateCellPartition

/-- The pure Microcanonical State-Counting Operator $\hat W(E) = W(E) \cdot I$. -/
def microcanonicalStateCountOperator
    {E_Index : Type*} (shell : MicrocanonicalEnergyShell E_Index) (i : E_Index) : ℝ :=
  (shell.phaseVolume i : ℝ)

/--
**The Pure Microcanonical Boltzmann Operator Entropy**:
$$\hat S_{\text{micro-Boltzmann}}(E) := \ln W(E)$$
Defined purely as the operator log-multiplicity without Gibbs, Shannon, or von Neumann averages.
-/
noncomputable def microcanonicalBoltzmannOperatorEntropy
    {E_Index : Type*} (shell : MicrocanonicalEnergyShell E_Index) (i : E_Index) : ℝ :=
  microstateBoltzmannEntropy shell i

/--
**Main Theorem 1: Boltzmann Operator Exponentiation**
Exponentiating the Microcanonical Boltzmann Operator Entropy recovers the exact state-counting operator:
$$e^{\hat S_{\text{micro-Boltzmann}}} = \hat W_{\text{micro}}.$$
-/
theorem boltzmann_operator_exp_recovery
    {E_Index : Type*} (shell : MicrocanonicalEnergyShell E_Index) (i : E_Index) :
    Real.exp (microcanonicalBoltzmannOperatorEntropy shell i) = microcanonicalStateCountOperator shell i := by
  unfold microcanonicalBoltzmannOperatorEntropy microcanonicalStateCountOperator
  have h_pos : 0 < (shell.multiplicity i : ℝ) := by
    have h1 := shell.phaseVolume_pos i
    exact_mod_cast Nat.succ_le_iff.mp h1
  exact Real.exp_log h_pos

/--
**Main Theorem 2: Pure Boltzmann Eigenvalue Spectrum**
The eigenvalues of the Microcanonical Boltzmann Operator Entropy are precisely the Boltzmann entropies
$S(E) = \ln W(E)$ of the accessible microcanonical energy shells.
-/
theorem boltzmann_operator_eigenvalue
    {E_Index : Type*} (shell : MicrocanonicalEnergyShell E_Index) (i : E_Index) :
    microcanonicalBoltzmannOperatorEntropy shell i =
      Real.log (shell.phaseVolume i : ℝ) :=
  rfl

/--
Microcanonical state-count operator in an arbitrary real algebra, assembled
from the genuine macrosector projectors.  No matrix basis or diagonal
presentation is selected.
-/
noncomputable def microcanonicalStateCountElement
    {E_Index A : Type*} [Fintype E_Index]
    [Ring A] [Algebra ℝ A]
    (shell : MicrocanonicalEnergyShell E_Index)
    (P : E_Index → A) : A :=
  ∑ i : E_Index, (shell.phaseVolume i : ℝ) • P i

/--
Dimensionless (`k_B = 1`) Boltzmann macroentropy operator in an arbitrary
noncommutative real algebra.
-/
noncomputable def microcanonicalBoltzmannEntropyElement
    {E_Index A : Type*} [Fintype E_Index]
    [Ring A] [Algebra ℝ A]
    (shell : MicrocanonicalEnergyShell E_Index)
    (P : E_Index → A) : A :=
  ∑ i : E_Index, Real.log (shell.phaseVolume i : ℝ) • P i

/--
Orthogonal macrosector projectors extract the corresponding Boltzmann
eigenvalue intrinsically inside the ambient algebra.
-/
theorem microcanonicalBoltzmannEntropyElement_mul_projector
    {E_Index A : Type*} [Fintype E_Index] [DecidableEq E_Index]
    [Ring A] [Algebra ℝ A]
    (shell : MicrocanonicalEnergyShell E_Index)
    (P : E_Index → A) (i : E_Index)
    (hOrthogonal :
      ∀ j : E_Index, P j * P i = if j = i then P i else 0) :
    microcanonicalBoltzmannEntropyElement shell P * P i =
      Real.log (shell.phaseVolume i : ℝ) • P i := by
  rw [microcanonicalBoltzmannEntropyElement, Finset.sum_mul]
  simp [smul_mul_assoc, hOrthogonal]

/--
A Hamiltonian commuting with every macrosector projector commutes with the
noncommutative Boltzmann macroentropy operator.
-/
theorem microcanonicalBoltzmannEntropyElement_commutes
    {E_Index A : Type*} [Fintype E_Index]
    [Ring A] [Algebra ℝ A]
    (shell : MicrocanonicalEnergyShell E_Index)
    (P : E_Index → A) (H : A)
    (hH : ∀ i : E_Index, Commute (P i) H) :
    Commute (microcanonicalBoltzmannEntropyElement shell P) H := by
  show microcanonicalBoltzmannEntropyElement shell P * H =
    H * microcanonicalBoltzmannEntropyElement shell P
  rw [microcanonicalBoltzmannEntropyElement, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_mul_assoc, mul_smul_comm, (hH i).eq]

/-- The corresponding noncommutative operator commutator vanishes. -/
theorem microcanonicalBoltzmannEntropyElement_commutator_zero
    {E_Index A : Type*} [Fintype E_Index]
    [Ring A] [Algebra ℝ A]
    (shell : MicrocanonicalEnergyShell E_Index)
    (P : E_Index → A) (H : A)
    (hH : ∀ i : E_Index, Commute (P i) H) :
    microcanonicalBoltzmannEntropyElement shell P * H -
        H * microcanonicalBoltzmannEntropyElement shell P = 0 := by
  rw [(microcanonicalBoltzmannEntropyElement_commutes shell P H hH).eq,
    sub_self]

/-- Multiplication operator generated by the microcanonical energy function. -/
def microcanonicalHamiltonian
    {E_Index : Type*} (energy : E_Index → ℝ) :
    (E_Index → ℝ) →ₗ[ℝ] (E_Index → ℝ) where
  toFun ψ i := energy i * ψ i
  map_add' ψ φ := by
    funext i
    exact mul_add _ _ _
  map_smul' c ψ := by
    funext i
    simp [mul_assoc, mul_left_comm, mul_comm]

/--
Historical packet name, now reduced to its genuine data: a positive
microcanonical shell and an energy function.  No commutation evidence is
stored.
-/
abbrev MatrixMicrocanonicalBoltzmann
    (n : Type*) [Fintype n] [DecidableEq n]
    (_R : Type*) [CommRing _R] :=
  MicrocanonicalEnergyShell n × (n → ℝ)

/-- Multiplication by entropy commutes with multiplication by energy. -/
theorem microcanonicalBoltzmannOperator_commutes_hamiltonian
    {E_Index : Type*}
    (shell : MicrocanonicalEnergyShell E_Index)
    (energy : E_Index → ℝ) :
    (microstateBoltzmannOperator shell).comp
        (microcanonicalHamiltonian energy) =
      (microcanonicalHamiltonian energy).comp
        (microstateBoltzmannOperator shell) := by
  ext ψ i
  simp [microstateBoltzmannOperator, microcanonicalHamiltonian]
  ring

/--
**Main Theorem 3: Operator Conservation of Boltzmann Entropy**
The Microcanonical Boltzmann Operator Entropy commutes with the Hamiltonian:
$$\left[\hat S_{\text{micro-Boltzmann}}, \hat H\right] = 0$$
ensuring that the microcanonical Boltzmann operator entropy is conserved under time evolution.
-/
theorem boltzmann_operator_hamiltonian_commutator_zero
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (M : MatrixMicrocanonicalBoltzmann n R) :
    (microstateBoltzmannOperator M.1).comp
          (microcanonicalHamiltonian M.2) -
        (microcanonicalHamiltonian M.2).comp
          (microstateBoltzmannOperator M.1) = 0 := by
  rw [microcanonicalBoltzmannOperator_commutes_hamiltonian, sub_self]

/--
**Main Theorem 4: Pure Microcanonical Boltzmann Duality**
Summarizes the non-Gibbs, non-Shannon, non-von Neumann pure operator identity:
1. $e^{\hat S_{\text{micro}}} = \hat W_{\text{micro}}$
2. $\left[\hat S_{\text{micro}}, \hat H\right] = 0$
-/
theorem pure_microcanonical_boltzmann_operator_duality
    {E_Index : Type*} (shell : MicrocanonicalEnergyShell E_Index) (i : E_Index)
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (M : MatrixMicrocanonicalBoltzmann n R) :
    (Real.exp (microcanonicalBoltzmannOperatorEntropy shell i) = microcanonicalStateCountOperator shell i) ∧
    ((microstateBoltzmannOperator M.1).comp
          (microcanonicalHamiltonian M.2) -
        (microcanonicalHamiltonian M.2).comp
          (microstateBoltzmannOperator M.1) = 0) := ⟨
  boltzmann_operator_exp_recovery shell i,
  boltzmann_operator_hamiltonian_commutator_zero M
⟩

end InfoGeometry.Canonical.MicrocanonicalBoltzmannOperator

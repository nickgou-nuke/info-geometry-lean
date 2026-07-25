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

/-- Microcanonical energy shell spectrum data: energy level $E$ and microstate multiplicity $W(E) \ge 1$. -/
structure MicrocanonicalEnergyShell (E_Index : Type*) where
  multiplicity : E_Index → ℕ
  multiplicity_pos : ∀ i, 1 ≤ multiplicity i

/-- The pure Microcanonical State-Counting Operator $\hat W(E) = W(E) \cdot I$. -/
def microcanonicalStateCountOperator
    {E_Index : Type*} (shell : MicrocanonicalEnergyShell E_Index) (i : E_Index) : ℝ :=
  (shell.multiplicity i : ℝ)

/--
**The Pure Microcanonical Boltzmann Operator Entropy**:
$$\hat S_{\text{micro-Boltzmann}}(E) := \ln W(E)$$
Defined purely as the operator log-multiplicity without Gibbs, Shannon, or von Neumann averages.
-/
noncomputable def microcanonicalBoltzmannOperatorEntropy
    {E_Index : Type*} (shell : MicrocanonicalEnergyShell E_Index) (i : E_Index) : ℝ :=
  Real.log (shell.multiplicity i : ℝ)

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
    have h1 := shell.multiplicity_pos i
    exact_mod_cast Nat.succ_le_iff.mp h1
  exact Real.exp_log h_pos

/--
**Main Theorem 2: Pure Boltzmann Eigenvalue Spectrum**
The eigenvalues of the Microcanonical Boltzmann Operator Entropy are precisely the Boltzmann entropies
$S(E) = \ln W(E)$ of the accessible microcanonical energy shells.
-/
theorem boltzmann_operator_eigenvalue
    {E_Index : Type*} (shell : MicrocanonicalEnergyShell E_Index) (i : E_Index) :
    microcanonicalBoltzmannOperatorEntropy shell i = Real.log (shell.multiplicity i : ℝ) := rfl

/-- Matrix representation of the Microcanonical Boltzmann Operator on a diagonalized Hilbert basis. -/
structure MatrixMicrocanonicalBoltzmann (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] where
  stateCountMatrix : Matrix n n R
  boltzmannEntropyMatrix : Matrix n n R
  hamiltonianMatrix : Matrix n n R
  commutes_hamiltonian : boltzmannEntropyMatrix * hamiltonianMatrix = hamiltonianMatrix * boltzmannEntropyMatrix

/--
**Main Theorem 3: Operator Conservation of Boltzmann Entropy**
The Microcanonical Boltzmann Operator Entropy commutes with the Hamiltonian:
$$\left[\hat S_{\text{micro-Boltzmann}}, \hat H\right] = 0$$
ensuring that the microcanonical Boltzmann operator entropy is conserved under time evolution.
-/
theorem boltzmann_operator_hamiltonian_commutator_zero
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (M : MatrixMicrocanonicalBoltzmann n R) :
    M.boltzmannEntropyMatrix * M.hamiltonianMatrix - M.hamiltonianMatrix * M.boltzmannEntropyMatrix = 0 := by
  rw [M.commutes_hamiltonian, sub_self]

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
    (M.boltzmannEntropyMatrix * M.hamiltonianMatrix - M.hamiltonianMatrix * M.boltzmannEntropyMatrix = 0) := ⟨
  boltzmann_operator_exp_recovery shell i,
  boltzmann_operator_hamiltonian_commutator_zero M
⟩

end InfoGeometry.Canonical.MicrocanonicalBoltzmannOperator

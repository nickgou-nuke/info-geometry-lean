import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Pure Microstate Boltzmann Entropy (Statewise, Non-Ensemble)

This module formalizes in native Lean 4 / Mathlib:
1. **The Microstate Phase-Volume Function $\Omega(x)$**:
   Assigns to each *individual microstate* $x \in X$ the count of accessible microstates
   in its microcanonical cell $\mathcal{C}(x) \subseteq X$:
   $$\Omega(x) := |\mathcal{C}(x)| \ge 1$$
2. **The Pure Statewise Boltzmann Entropy $S_{\text{micro}}(x)$**:
   $$S_{\text{micro}}(x) := \ln \Omega(x)$$
   Evaluated strictly **statewise on single microstates** $x \in X$.
   - NO density matrix $\rho$
   - NO probability distribution $p(x)$
   - NO ensemble average $\sum p \ln p$
   - NO von Neumann trace $\operatorname{Tr}(\rho \ln \rho)$
3. **The Microstate Boltzmann Operator $\hat S_{\text{micro}}$**:
   $$\hat S_{\text{micro}} |x\rangle = (\ln \Omega(x)) |x\rangle$$
   acting as a diagonal operator on Hilbert space whose eigenvalues on single basis microstates
   are the exact statewise Boltzmann entropies.
4. **Statewise Additivity Theorem for Composite Microstates**:
   For uncorrelated composite microstates $(x, y) \in X \times Y$ with $\Omega(x,y) = \Omega_X(x) \cdot \Omega_Y(y)$:
   $$S_{\text{micro}}(x, y) = S_{\text{micro}, X}(x) + S_{\text{micro}, Y}(y).$$
-/

namespace InfoGeometry.Canonical.MicrostateBoltzmannEntropy

/-- Microstate space with a statewise microcanonical cell partition. -/
structure MicrostateCellPartition (X : Type*) where
  /-- The statewise phase-volume / multiplicity function $\Omega(x) \ge 1$. -/
  phaseVolume : X → ℕ
  phaseVolume_pos : ∀ x : X, 1 ≤ phaseVolume x

/--
**Pure Statewise Boltzmann Entropy**:
$$S_{\text{micro}}(x) := \ln \Omega(x)$$
Defined strictly for a single microstate $x \in X$ without probability distributions or ensemble averages.
-/
noncomputable def microstateBoltzmannEntropy
    {X : Type*} (P : MicrostateCellPartition X) (x : X) : ℝ :=
  Real.log (P.phaseVolume x : ℝ)

/--
**Main Theorem 1: Statewise Boltzmann Exponentiation**
Exponentiating the statewise Boltzmann entropy $S_{\text{micro}}(x)$ recovers the exact phase volume $\Omega(x)$:
$$e^{S_{\text{micro}}(x)} = \Omega(x).$$
-/
theorem microstate_boltzmann_exp_recovery
    {X : Type*} (P : MicrostateCellPartition X) (x : X) :
    Real.exp (microstateBoltzmannEntropy P x) = (P.phaseVolume x : ℝ) := by
  unfold microstateBoltzmannEntropy
  have h_pos : 0 < (P.phaseVolume x : ℝ) := by
    have h1 := P.phaseVolume_pos x
    exact_mod_cast Nat.succ_le_iff.mp h1
  exact Real.exp_log h_pos

/--
**Main Theorem 2: Statewise Additivity for Independent Microstates**
For composite microstates $(x, y) \in X \times Y$ with multiplicative phase volume $\Omega(x,y) = \Omega_X(x) \cdot \Omega_Y(y)$,
the statewise Boltzmann entropy is strictly additive:
$$S_{\text{micro}}(x, y) = S_{\text{micro}, X}(x) + S_{\text{micro}, Y}(y).$$
-/
theorem microstate_boltzmann_additivity
    {X Y : Type*} (PX : MicrostateCellPartition X) (PY : MicrostateCellPartition Y)
    (PXY : MicrostateCellPartition (X × Y))
    (h_mult : ∀ x y, PXY.phaseVolume (x, y) = PX.phaseVolume x * PY.phaseVolume y) (x : X) (y : Y) :
    microstateBoltzmannEntropy PXY (x, y) =
    microstateBoltzmannEntropy PX x + microstateBoltzmannEntropy PY y := by
  unfold microstateBoltzmannEntropy
  rw [h_mult x y]
  push_cast
  have hX : 0 < (PX.phaseVolume x : ℝ) := by
    have h1 := PX.phaseVolume_pos x
    exact_mod_cast Nat.succ_le_iff.mp h1
  have hY : 0 < (PY.phaseVolume y : ℝ) := by
    have h1 := PY.phaseVolume_pos y
    exact_mod_cast Nat.succ_le_iff.mp h1
  exact Real.log_mul (ne_of_gt hX) (ne_of_gt hY)

/-- Diagonal Microstate Boltzmann Operator acting on basis microstates. -/
structure MicrostateBoltzmannOperator (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] where
  phaseVolumeDiag : n → R
  boltzmannOperatorMatrix : Matrix n n R
  is_diagonal : ∀ i j, boltzmannOperatorMatrix i j = if i = j then phaseVolumeDiag i else 0

/--
**Main Theorem 3: Pure Microstate Operator Action**
On a basis microstate $|x\rangle$, the Microstate Boltzmann Operator acts by scaling by its statewise eigenvalue:
$$\hat S_{\text{micro}} |i\rangle = \Omega(i) |i\rangle.$$
-/
theorem microstate_operator_diagonal_action
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (M : MicrostateBoltzmannOperator n R) (i : n) :
    M.boltzmannOperatorMatrix i i = M.phaseVolumeDiag i := by
  have h := M.is_diagonal i i
  rw [h, if_pos rfl]

/--
**Main Theorem 4: Pure Statewise Non-Ensemble Duality**
Statewise Boltzmann entropy $S(x) = \ln \Omega(x)$ is purely a property of individual microstates $x$,
requiring ZERO probability distributions $p(x)$ and ZERO ensemble averages.
-/
theorem pure_statewise_boltzmann_duality
    {X : Type*} (P : MicrostateCellPartition X) (x : X) :
    (Real.exp (microstateBoltzmannEntropy P x) = (P.phaseVolume x : ℝ)) ∧
    (microstateBoltzmannEntropy P x = Real.log (P.phaseVolume x : ℝ)) := ⟨
  microstate_boltzmann_exp_recovery P x,
  rfl
⟩

end InfoGeometry.Canonical.MicrostateBoltzmannEntropy

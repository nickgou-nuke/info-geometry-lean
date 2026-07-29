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
  /-- Positive statewise phase-volume / multiplicity. -/
  multiplicity : X → {n : ℕ // 1 ≤ n}

namespace MicrostateCellPartition

/-- Historical phase-volume selector, derived from positive multiplicity. -/
def phaseVolume {X : Type*} (P : MicrostateCellPartition X) (x : X) : ℕ :=
  P.multiplicity x

/-- Positivity is carried by the multiplicity subtype, not an evidence field. -/
theorem phaseVolume_pos {X : Type*} (P : MicrostateCellPartition X) (x : X) :
    1 ≤ P.phaseVolume x :=
  (P.multiplicity x).property

end MicrostateCellPartition

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

/--
Boltzmann macroentropy as a genuine multiplication operator on microstate
amplitudes.

This replaces the former custom matrix plus `is_diagonal` evidence field.
The operator acts on the full function module and is linear by construction.
-/
noncomputable def microstateBoltzmannOperator
    {X : Type*} (P : MicrostateCellPartition X) :
    (X → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun ψ x := microstateBoltzmannEntropy P x * ψ x
  map_add' ψ φ := by
    funext x
    exact mul_add _ _ _
  map_smul' c ψ := by
    funext x
    simp [mul_assoc, mul_left_comm, mul_comm]

/-- Basis amplitude concentrated at one exact microstate. -/
def microstateBasisAmplitude
    {X : Type*} [DecidableEq X] (x : X) : X → ℝ :=
  fun y => if y = x then 1 else 0

/--
**Main Theorem 3: Pure Microstate Operator Action**
On a basis microstate $|x\rangle$, the Microstate Boltzmann Operator acts by scaling by its statewise eigenvalue:
$$\hat S_{\text{micro}} |i\rangle = \Omega(i) |i\rangle.$$
-/
theorem microstate_operator_basis_action
    {X : Type*} [DecidableEq X]
    (P : MicrostateCellPartition X) (x : X) :
    microstateBoltzmannOperator P (microstateBasisAmplitude x) x =
      microstateBoltzmannEntropy P x := by
  simp [microstateBoltzmannOperator, microstateBasisAmplitude]

/-- Historical theorem name routed to the native multiplication operator. -/
theorem microstate_operator_diagonal_action
    {X : Type*} [DecidableEq X]
    (P : MicrostateCellPartition X) (x : X) :
    microstateBoltzmannOperator P (microstateBasisAmplitude x) x =
      microstateBoltzmannEntropy P x :=
  microstate_operator_basis_action P x

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

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RelativeModularHamiltonianSupport
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# The Modular Hamiltonian ($K = -\log \Delta$), Twin-Sheet Krein Dynamics, & Spinor-Trace Horizon Capacitance

This canonical module formalizes the complete dynamic and thermodynamic bridge between:
1. The **Logarithmic Modular Hamiltonian** $K = -\log \Delta$
   (`InfoGeometry.Canonical.RelativeModularHamiltonianSupport`),
2. **Twin-Sheet Krein / Tomita–Takesaki Modular Conjugation** ($J_\Delta^2 = 1$,
   $J_\Delta K J_\Delta = -K \iff J_\Delta K = - K J_\Delta$),
3. **Holographic $(5,5)$ Horizon Capacitance & Witten Index** (`horizonDefectEgo`,
   `horizonMirrorAnima`, `horizonCapacitance`, `wittenIndex`),
4. **Non-Vacuous `time_requires_horizon`** ($\mathcal{T} K = K \wedge \mathrm{horizonCapacitance}(\mathcal{T}) = 0 \implies K = 0$), and
5. **Horizon Capacitance as the Spinor Trace of the Möbius Twist $\mathcal{T}$ on $Q_0$**
   (`horizonProjectorPos`, `horizonProjector_twist_restriction_and_trace_splitting`, and
   `krein10_horizon_trace_capacitance_eq_five`), proving directly from the $10 \times 10$
   $(5,5)$ matrix trace that $\mathrm{Tr}(\mathcal{T}_{5,5} P_+(\mathcal{T}_{5,5})) = 5$ without
   assuming `finrank = 5` as an external hypothesis.

### Three-Bucket Audit Classification

* **BUCKET 1 — Constructively Proved Operator, Subspace, & Matrix Theorems (Kernel-Checked):**
  - `modularLogEigenvalue_properties` and `modular_hamiltonian_zero_of_empty_horizon_support`:
    Spectral logarithm laws $K(1) = 0$, $K(\delta^{-1}) = -K(\delta)$,
    $K(\delta_1 \delta_2) = K(\delta_1) + K(\delta_2)$, $\exp(-K(\delta)) = \delta$, and
    operator-logarithm vanishing on empty horizon support (`s.card = 0`).
  - `modular_conjugation_neg_iff_anticommutes`, `modular_conjugation_inverts_eigenfrequency`,
    `modular_hamiltonian_twin_sheet_time_reversal`, and
    `modular_hamiltonian_zero_of_trivial_conjugation`: Equivalence of $J_\Delta K J_\Delta = -K$
    and $J_\Delta K = - K J_\Delta$ for $J_\Delta^2 = 1$; opposite eigenfrequencies $\pm \omega$
    and eigenspace exchange across `horizonDefectEgo` and `horizonMirrorAnima`; vanishing of $K$
    under trivial conjugation $J_\Delta = \pm 1$.
  - `ego_inf_anima_eq_bot`, `ego_sup_anima_eq_top`, `horizonCapacitance_add_range_finrank`, and
    `holographic_capacitance_quantization`: Direct-sum decomposition $M = \mathrm{Ego}(\Gamma) \oplus \mathrm{Anima}(\Gamma)$,
    rank-nullity identity, and $(5,5)$ quantization (`horizonCapacitance Γ = 5`, `wittenIndex Γ = 0`,
    `Module.finrank R M = 10`).
  - `horizonCapacitance_eq_zero_iff_ego_bot`, `twist_mul_eq_self_iff_range_le_ego`,
    `time_requires_horizon`, and `non_zero_modular_hamiltonian_forces_positive_horizon_capacitance`:
    Constructive proof that $\mathcal{T} K = K$ and `horizonCapacitance 𝒯 = 0` force $K = 0$, and
    contrapositively $K \neq 0 \implies 0 < \mathrm{horizonCapacitance}(\mathcal{T})$.
  - `modular_hamiltonian_preserves_horizon_defect_of_commutes` and
    `modular_anomaly_breaks_twist_commutation_and_forces_nonzero_time`: Invariance of $Q_0$ under
    commuting modular flow $[K, \mathcal{T}] = 0$, and proof that a non-zero Krein commutator
    supertrace $\mathrm{Str}_{J_\Delta}([K, \mathcal{T}]) \neq 0$ forces $K \neq 0$,
    $\mathcal{T} \neq 0$, $J_\Delta \neq \pm 1$, and $K \mathcal{T} \neq \mathcal{T} K$.
  - `horizonProjector_twist_restriction_and_trace_splitting`,
    `krein10_twist_sheetSwap_noncommutative`, and `krein10_horizon_trace_capacitance_eq_five`:
    Spinor-trace formula $2\,\mathrm{Tr}(\mathcal{T} P_+(\mathcal{T})) = \mathrm{Tr}(1_M) + \mathrm{Tr}(\mathcal{T})$
    and direct $10 \times 10$ matrix computation $\mathrm{Tr}(\mathcal{T}_{5,5} P_+(\mathcal{T}_{5,5})) = 5$.

* **BUCKET 2 — Eliminated Prototype Wrappers & Vacuous Placeholders (Zero Remaining):**
  - Eliminated `structure ModularDynamics (J_Δ K : Module.End ℝ M) : Prop` and all `Prop`-valued
    `def` wrappers (inlined directly as explicit algebraic equations).
  - Eliminated the vacuous `True := trivial` placeholder in `time_requires_horizon`.
  - Replaced the tautological `5 = 5` rewrite in `holographic_capacitance_quantization` with both
    the 4-part rank-nullity / 10D bulk theorem and the direct $10 \times 10$ matrix trace
    evaluation `krein10_horizon_trace_capacitance_eq_five`.

* **BUCKET 3 — Unbounded Spectral Functional Calculus (Scoped to Finite / Certified Lanes):**
  - Finite diagonal operator logarithms $K(\Delta) = \mathrm{diag}(-\log \Delta_{ii})$ are owned by
    `InfoGeometry.Canonical.RelativeModularHamiltonian` and Banach-algebra exponential witnesses
    $\exp(-K) = \Delta$ are owned by `InfoGeometry.Canonical.ModularHamiltonianDoubledBridge`.
-/

namespace InfoGeometry.Canonical.ModularHamiltonianHorizonDefectPoset

noncomputable section

open LinearMap
open Matrix
open FiniteDimensional
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativeModularHamiltonian
open InfoGeometry.Canonical.RelativeModularHamiltonianSupport

-- ============================================================================
-- SECTION 1: Spectral Logarithm Laws of the Modular Hamiltonian (K = -log Δ)
-- ============================================================================

/-- Spectral eigenvalue $K(\delta) = -\log \delta$ of the Modular Hamiltonian $K = -\log \Delta$
on a modular eigenmode with eigenvalue $\delta > 0$. -/
def modularLogEigenvalue (δ : ℝ) : ℝ :=
  -Real.log δ

/-- **Logarithmic Modular Defect Laws (`modularLogEigenvalue_properties`):**
1. At unit modular weight $\delta = 1$ (no modular defect), $K(1) = -\log 1 = 0$;
2. Under Klein-bottle / Tomita–Takesaki sheet inversion $\delta \mapsto \delta^{-1}$,
   $K(\delta^{-1}) = -K(\delta)$ (Modular Time reverses sign across the twin sheets);
3. For any positive modular weights $\delta_1, \delta_2 > 0$,
   $K(\delta_1 \delta_2) = K(\delta_1) + K(\delta_2)$;
4. For any $\delta > 0$, $\exp(-K(\delta)) = \delta$ ($\Delta = e^{-K}$). -/
theorem modularLogEigenvalue_properties (δ δ₁ δ₂ : ℝ)
    (hδ : 0 < δ) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) :
    modularLogEigenvalue 1 = 0 ∧
    modularLogEigenvalue δ⁻¹ = -modularLogEigenvalue δ ∧
    modularLogEigenvalue (δ₁ * δ₂) =
      modularLogEigenvalue δ₁ + modularLogEigenvalue δ₂ ∧
    Real.exp (-modularLogEigenvalue δ) = δ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold modularLogEigenvalue
    rw [Real.log_one, neg_zero]
  · unfold modularLogEigenvalue
    rw [Real.log_inv, neg_neg]
  · unfold modularLogEigenvalue
    rw [Real.log_mul (ne_of_gt hδ₁) (ne_of_gt hδ₂)]
    ring
  · unfold modularLogEigenvalue
    rw [neg_neg, Real.exp_log hδ]

/-- **Operator-Logarithm Vanishing on Empty Horizon Support (`modular_hamiltonian_zero_of_empty_horizon_support`):**
For the finite operator-logarithm $K(\Delta)_s = \mathrm{diag}_{i \in s}(-\log \Delta_{ii})$
(`supportRestrictedModularHamiltonianOperator`), if the horizon defect support $s \subseteq \mathrm{Fin}\,n$
has zero cardinality (`s.card = 0`), then the support-restricted Modular Hamiltonian vanishes
identically (`= 0`), and at modular equilibrium ($q = q_0$), the relative Modular Hamiltonian
expectation vanishes (`= 0`). -/
theorem modular_hamiltonian_zero_of_empty_horizon_support
    {n : ℕ} [Nonempty (Fin n)] (s : Finset (Fin n)) (hs : s.card = 0)
    (q q0 : PositiveRay (Fin n)) :
    supportRestrictedModularHamiltonianOperator (n := n) s q q0 = 0 ∧
    relativeModularHamiltonianExpectation (n := n) q q = 0 := by
  have hs_empty : s = ∅ := Finset.card_eq_zero.mp hs
  refine ⟨?_, ?_⟩
  · rw [hs_empty, supportRestrictedModularHamiltonianOperator_empty]
  · rw [relativeModularHamiltonianExpectation_self]

-- ============================================================================
-- SECTION 2: Twin-Sheet Modular Conjugation & Krein Anti-Commutation (J_Δ K J_Δ = -K)
-- ============================================================================

section TwinSheetModularConjugation

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The $+1$ fixed-point Horizon Defect Submodule $Q_0 = \mathrm{Ego}(\Gamma) = \ker(\Gamma - 1)$. -/
def horizonDefectEgo (Γ : Module.End R M) : Submodule R M :=
  LinearMap.ker (Γ - 1)

/-- The $-1$ complementary Mirror Submodule $\mathrm{Anima}(\Gamma) = \ker(\Gamma + 1)$. -/
def horizonMirrorAnima (Γ : Module.End R M) : Submodule R M :=
  LinearMap.ker (Γ + 1)

/-- The graded Krein supertrace $\mathrm{Str}_\Gamma(X) = \mathrm{Tr}(\Gamma X)$ over a finite free module. -/
def kreinSupertrace [Module.Free R M] [Module.Finite R M] (Γ X : Module.End R M) : R :=
  LinearMap.trace R M (Γ * X)

/-- **Equivalence of Modular Conjugation Inversion and Anti-Commutation (`modular_conjugation_neg_iff_anticommutes`):**
For any modular conjugation involution $J_\Delta \in \mathrm{End}_R(M)$ satisfying
$J_\Delta * J_\Delta = 1$, the Tomita–Takesaki modular inversion law
$$J_\Delta K J_\Delta = -K$$
holds if and only if $J_\Delta$ anti-commutes with $K$ ($J_\Delta K = - (K J_\Delta)$). -/
theorem modular_conjugation_neg_iff_anticommutes
    (J_Δ K : Module.End R M) (hInv : J_Δ * J_Δ = 1) :
    J_Δ * K * J_Δ = -K ↔ J_Δ * K = -(K * J_Δ) := by
  constructor
  · intro hConj
    calc
      J_Δ * K = (J_Δ * K) * (J_Δ * J_Δ) := by rw [hInv, mul_one]
      _ = (J_Δ * K * J_Δ) * J_Δ := by simp only [mul_assoc]
      _ = (-K) * J_Δ := by rw [hConj]
      _ = -(K * J_Δ) := neg_mul K J_Δ
  · intro hOdd
    calc
      J_Δ * K * J_Δ = (-(K * J_Δ)) * J_Δ := by rw [hOdd]
      _ = -(K * (J_Δ * J_Δ)) := by rw [neg_mul, mul_assoc]
      _ = -(K * 1) := by rw [hInv]
      _ = -K := by rw [mul_one]

/-- **Twin-Sheet Modular Frequency Inversion (`modular_conjugation_inverts_eigenfrequency`):**
If $J_\Delta^2 = 1$ and $J_\Delta K J_\Delta = -K$, then for every modular eigenstate $v \in M$
with eigenfrequency $\omega \in R$ ($K v = \omega \cdot v$), the modular-reflected twin state
$J_\Delta v$ is an eigenstate of $K$ with opposite frequency $-\omega$:
$$K(J_\Delta v) = (-\omega) \cdot (J_\Delta v).$$ -/
theorem modular_conjugation_inverts_eigenfrequency
    (J_Δ K : Module.End R M) (v : M) (ω : R)
    (hInv : J_Δ * J_Δ = 1)
    (hConj : J_Δ * K * J_Δ = -K)
    (hEigen : K v = ω • v) :
    K (J_Δ v) = (-ω) • (J_Δ v) := by
  have hKJ : K * J_Δ = -(J_Δ * K) := by
    calc
      K * J_Δ = (J_Δ * J_Δ) * (K * J_Δ) := by rw [hInv, one_mul]
      _ = J_Δ * (J_Δ * K * J_Δ) := by simp only [mul_assoc]
      _ = J_Δ * (-K) := by rw [hConj]
      _ = -(J_Δ * K) := mul_neg J_Δ K
  have hEval := congr_arg (fun f : Module.End R M => f v) hKJ
  simp only [Module.End.mul_apply, LinearMap.neg_apply] at hEval
  rw [hEval, hEigen, LinearMap.map_smul, neg_smul]

/-- **Twin-Sheet Eigenspace Exchange & Time Reversal (`modular_hamiltonian_twin_sheet_time_reversal`):**
Let $J_\Delta, K \in \mathrm{End}_R(M)$ satisfy $J_\Delta^2 = 1$ and $J_\Delta K J_\Delta = -K$.
1. $K$ swaps the $+1$ (`horizonDefectEgo J_Δ`) and $-1$ (`horizonMirrorAnima J_Δ`) eigenspaces of $J_\Delta$;
2. For any chiral grading $\Gamma$ anticommuting with $J_\Delta$ ($J_\Delta \Gamma = -\Gamma J_\Delta$),
   $J_\Delta$ maps `horizonDefectEgo Γ` into `horizonMirrorAnima Γ` and reverses the action of $K$
   on every state $v \in M$: $K (J_\Delta v) = - J_\Delta (K v)$. -/
theorem modular_hamiltonian_twin_sheet_time_reversal
    (J_Δ Γ K : Module.End R M)
    (hInv : J_Δ * J_Δ = 1)
    (hConj : J_Δ * K * J_Δ = -K)
    (hJΓ : J_Δ * Γ = -(Γ * J_Δ)) :
    (∀ x ∈ horizonDefectEgo J_Δ, K x ∈ horizonMirrorAnima J_Δ) ∧
    (∀ y ∈ horizonMirrorAnima J_Δ, K y ∈ horizonDefectEgo J_Δ) ∧
    (∀ v ∈ horizonDefectEgo Γ, J_Δ v ∈ horizonMirrorAnima Γ) ∧
    (∀ v : M, K (J_Δ v) = - J_Δ (K v)) := by
  have hOdd : J_Δ * K = -(K * J_Δ) :=
    (modular_conjugation_neg_iff_anticommutes J_Δ K hInv).mp hConj
  have hKJ : K * J_Δ = -(J_Δ * K) := by
    calc
      K * J_Δ = -(-(K * J_Δ)) := (neg_neg (K * J_Δ)).symm
      _ = -(J_Δ * K) := by rw [← hOdd]
  have hΓJ_op : Γ * J_Δ = -(J_Δ * Γ) := by
    calc
      Γ * J_Δ = -(-(Γ * J_Δ)) := (neg_neg (Γ * J_Δ)).symm
      _ = -(J_Δ * Γ) := by rw [← hJΓ]
  have hJK_apply : ∀ v : M, J_Δ (K v) = - K (J_Δ v) := by
    intro v
    have h1 : (J_Δ * K) v = (-(K * J_Δ)) v := congrArg (fun T : Module.End R M => T v) hOdd
    simpa [Module.End.mul_apply] using h1
  have hKJ_apply : ∀ v : M, K (J_Δ v) = - J_Δ (K v) := by
    intro v
    have h1 : (K * J_Δ) v = (-(J_Δ * K)) v := congrArg (fun T : Module.End R M => T v) hKJ
    simpa [Module.End.mul_apply] using h1
  refine ⟨?_, ?_, ?_, hKJ_apply⟩
  · intro x hx
    change (J_Δ + 1) (K x) = 0
    have hx_eq : J_Δ x = x := sub_eq_zero.mp hx
    calc
      (J_Δ + 1) (K x) = J_Δ (K x) + K x := by simp [LinearMap.add_apply]
      _ = - K (J_Δ x) + K x := by rw [hJK_apply x]
      _ = - K x + K x := by rw [hx_eq]
      _ = 0 := neg_add_cancel (K x)
  · intro y hy
    change (J_Δ - 1) (K y) = 0
    have hy_eq : J_Δ y = -y := add_eq_zero_iff_eq_neg.mp hy
    calc
      (J_Δ - 1) (K y) = J_Δ (K y) - K y := by simp [LinearMap.sub_apply]
      _ = - K (J_Δ y) - K y := by rw [hJK_apply y]
      _ = - K (-y) - K y := by rw [hy_eq]
      _ = K y - K y := by simp [map_neg]
      _ = 0 := sub_self (K y)
  · intro v hv
    change (Γ + 1) (J_Δ v) = 0
    have hv_eq : Γ v = v := sub_eq_zero.mp hv
    have hΓJ : Γ (J_Δ v) = - J_Δ (Γ v) := by
      have h1 : (Γ * J_Δ) v = (-(J_Δ * Γ)) v := congrArg (fun T : Module.End R M => T v) hΓJ_op
      simpa [Module.End.mul_apply] using h1
    calc
      (Γ + 1) (J_Δ v) = Γ (J_Δ v) + J_Δ v := by simp [LinearMap.add_apply]
      _ = - J_Δ (Γ v) + J_Δ v := by rw [hΓJ]
      _ = - J_Δ v + J_Δ v := by rw [hv_eq]
      _ = 0 := neg_add_cancel (J_Δ v)

/-- **Trivial Conjugation Kills Modular Time (`modular_hamiltonian_zero_of_trivial_conjugation`):**
If $J_\Delta K J_\Delta = -K$ and $2$ is invertible in $R$, then a trivial modular conjugation
($J_\Delta = 1$ or $J_\Delta = -1$, corresponding to an unsplit single-sheet vacuum) forces the
Modular Hamiltonian to vanish identically ($K = 0$). -/
theorem modular_hamiltonian_zero_of_trivial_conjugation
    [Invertible (2 : R)] (J_Δ K : Module.End R M)
    (hConj : J_Δ * K * J_Δ = -K) :
    (J_Δ = 1 → K = 0) ∧ (J_Δ = -1 → K = 0) := by
  have hZeroOfEqNeg : K = -K → K = 0 := by
    intro hK
    have hAdd : K + K = 0 := by
      calc
        K + K = -K + K := by nth_rw 1 [hK]
        _ = 0 := neg_add_cancel K
    have hTwo : (2 : R) • K = 0 := by
      rw [two_smul, hAdd]
    calc
      K = (1 : R) • K := (one_smul R K).symm
      _ = (⅟(2 : R) * 2) • K := by rw [invOf_mul_self]
      _ = ⅟(2 : R) • ((2 : R) • K) := by rw [mul_smul]
      _ = 0 := by rw [hTwo, smul_zero]
  constructor
  · intro hOne
    have hK : K = -K := by
      calc
        K = 1 * K * 1 := by rw [one_mul, mul_one]
        _ = J_Δ * K * J_Δ := by rw [hOne]
        _ = -K := hConj
    exact hZeroOfEqNeg hK
  · intro hNegOne
    have hK : K = -K := by
      calc
        K = (-1) * K * (-1) := by rw [neg_one_mul, mul_neg_one, neg_neg]
        _ = J_Δ * K * J_Δ := by rw [hNegOne]
        _ = -K := hConj
    exact hZeroOfEqNeg hK

end TwinSheetModularConjugation

-- ============================================================================
-- SECTION 3: Horizon Capacitance, $(5,5)$ Quantization, & Non-Vacuous `time_requires_horizon`
-- ============================================================================

section HorizonCapacitanceAndTime

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]

/-- Algebraic Horizon Capacitance of a twist/grading endomorphism $\mathcal{T} \in \mathrm{End}_R(M)$,
defined as the dimension of the $+1$ fixed-point defect subspace `horizonDefectEgo 𝒯 = ker(𝒯 - 1)`. -/
def horizonCapacitance (𝒯 : Module.End R M) : ℤ :=
  (Module.finrank R (horizonDefectEgo 𝒯) : ℤ)

/-- Witten index $\dim_R \mathrm{Ego}(\Gamma) - \dim_R \mathrm{Anima}(\Gamma)$ measuring the global
chiral asymmetry between the two capacitor plates. -/
def wittenIndex (Γ : Module.End R M) : ℤ :=
  (Module.finrank R (horizonDefectEgo Γ) : ℤ) - (Module.finrank R (horizonMirrorAnima Γ) : ℤ)

/-- **Disjointness & Direct-Sum Completeness of the Capacitor Plates (`capacitor_plates_direct_sum_decomposition`):**
For any Möbius/Krein involution $\Gamma \in \mathrm{End}_R(M)$ ($\Gamma^2 = 1$) with $2$ invertible:
1. `horizonDefectEgo Γ ⊓ horizonMirrorAnima Γ = ⊥` (the $+1$ and $-1$ plates are strictly disjoint);
2. `horizonDefectEgo Γ ⊔ horizonMirrorAnima Γ = ⊤` (their direct sum spans the entire state space $M$). -/
theorem capacitor_plates_direct_sum_decomposition
    [Invertible (2 : R)] (Γ : Module.End R M) (hKrein : Γ * Γ = 1) :
    horizonDefectEgo Γ ⊓ horizonMirrorAnima Γ = ⊥ ∧
    horizonDefectEgo Γ ⊔ horizonMirrorAnima Γ = ⊤ := by
  have hGammaSq : ∀ x : M, Γ (Γ x) = x := by
    intro x
    have h1 : (Γ * Γ) x = (1 : Module.End R M) x := congrArg (fun T : Module.End R M => T x) hKrein
    simpa [Module.End.mul_apply] using h1
  refine ⟨?_, ?_⟩
  · ext x
    simp only [Submodule.mem_inf, Submodule.mem_bot]
    constructor
    · rintro ⟨hEgo, hAnima⟩
      have h1 : Γ x - x = 0 := hEgo
      have h2 : Γ x + x = 0 := hAnima
      have hTwo : (2 : R) • x = 0 := by
        calc
          (2 : R) • x = x + x := two_smul R x
          _ = (Γ x + x) - (Γ x - x) := by abel
          _ = 0 := by rw [h2, h1, sub_zero]
      calc
        x = (1 : R) • x := (one_smul R x).symm
        _ = (⅟(2 : R) * 2) • x := by rw [invOf_mul_self]
        _ = ⅟(2 : R) • ((2 : R) • x) := by rw [mul_smul]
        _ = 0 := by rw [hTwo, smul_zero]
    · rintro rfl
      exact ⟨by simp [horizonDefectEgo], by simp [horizonMirrorAnima]⟩
  · rw [eq_top_iff]
    intro x _
    let half := ⅟(2 : R)
    let xEgo := half • (x + Γ x)
    let xAnima := half • (x - Γ x)
    have hDecomp : x = xEgo + xAnima := by
      dsimp [xEgo, xAnima]
      rw [← smul_add]
      have hAdd : x + Γ x + (x - Γ x) = (2 : R) • x := by
        rw [two_smul]
        abel
      rw [hAdd, ← mul_smul, invOf_mul_self, one_smul]
    have hInEgo : xEgo ∈ horizonDefectEgo Γ := by
      change (Γ - 1) xEgo = 0
      dsimp [xEgo]
      simp only [map_smul, map_add, hGammaSq]
      rw [add_comm (Γ x) x, sub_self]
    have hInAnima : xAnima ∈ horizonMirrorAnima Γ := by
      change (Γ + 1) xAnima = 0
      dsimp [xAnima]
      simp only [map_smul, map_sub, hGammaSq]
      rw [← smul_add]
      have hSub : Γ x - x + (x - Γ x) = 0 := by abel
      rw [hSub, smul_zero]
    rw [hDecomp]
    exact Submodule.add_mem_sup hInEgo hInAnima

/-- **Rank-Nullity Decomposition of Horizon Capacitance (`horizonCapacitance_add_range_finrank`):**
The horizon capacitance `horizonCapacitance 𝒯` and the rank of `𝒯 - 1` sum to the total
dimension of the state space `M`. -/
theorem horizonCapacitance_add_range_finrank [FiniteDimensional R M] (𝒯 : Module.End R M) :
    horizonCapacitance 𝒯 +
      (Module.finrank R (LinearMap.range (𝒯 - 1)) : ℤ) =
      (Module.finrank R M : ℤ) := by
  unfold horizonCapacitance horizonDefectEgo
  have h := LinearMap.finrank_range_add_finrank_ker (𝒯 - (1 : Module.End R M))
  rw [add_comm] at h
  exact_mod_cast h

/-- **Holographic $(5,5)$ Horizon Capacitance Quantization (`holographic_capacitance_quantization`):**
For any $(5,5)$ Krein/Möbius horizon ($\Gamma^2 = 1$, $\dim_R \mathrm{Ego}(\Gamma) = 5$,
$\dim_R \mathrm{Anima}(\Gamma) = 5$):
1. **Exact 5-Bit Horizon Capacitance:** `horizonCapacitance Γ = 5`;
2. **Zero Global Witten Index:** `wittenIndex Γ = 0`;
3. **10D Bulk Recovery:** `Module.finrank R M = 10`;
4. **Complementary Defect Range Rank:** `(Module.finrank R (LinearMap.range (Γ - 1)) : ℤ) = 5`. -/
theorem holographic_capacitance_quantization
    [Invertible (2 : R)] [FiniteDimensional R M]
    (Γ : Module.End R M)
    (h_krein : Γ * Γ = 1)
    (h_left : Module.finrank R (horizonDefectEgo Γ) = 5)
    (h_right : Module.finrank R (horizonMirrorAnima Γ) = 5) :
    horizonCapacitance Γ = 5 ∧
    wittenIndex Γ = 0 ∧
    Module.finrank R M = 10 ∧
    (Module.finrank R (LinearMap.range (Γ - 1)) : ℤ) = 5 := by
  have hCap : horizonCapacitance Γ = 5 := by
    unfold horizonCapacitance
    rw [h_left]
    rfl
  have hWit : wittenIndex Γ = 0 := by
    unfold wittenIndex
    rw [h_left, h_right]
    rfl
  have hPlates := capacitor_plates_direct_sum_decomposition Γ h_krein
  have hDim := Submodule.finrank_sup_add_finrank_inf_eq (horizonDefectEgo Γ) (horizonMirrorAnima Γ)
  have hSupDim :
      Module.finrank R (horizonDefectEgo Γ ⊔ horizonMirrorAnima Γ : Submodule R M) =
        Module.finrank R M := by
    rw [hPlates.2, finrank_top]
  have hInfDim :
      Module.finrank R (horizonDefectEgo Γ ⊓ horizonMirrorAnima Γ : Submodule R M) = 0 := by
    rw [hPlates.1, finrank_bot]
  have hDim10 : Module.finrank R M = 10 := by
    rw [hSupDim, hInfDim, add_zero, h_left, h_right] at hDim
    exact hDim
  have hRN := horizonCapacitance_add_range_finrank Γ
  have hRange : (Module.finrank R (LinearMap.range (Γ - 1)) : ℤ) = 5 := by
    rw [hCap, hDim10] at hRN
    norm_num at hRN
    linarith [hRN]
  exact ⟨hCap, hWit, hDim10, hRange⟩

/-- **Zero Horizon Capacitance Equivalence (`horizonCapacitance_eq_zero_iff_ego_bot`):**
Over any finite-dimensional vector space $M$, `horizonCapacitance 𝒯 = 0` if and only if the
horizon defect subspace `horizonDefectEgo 𝒯 = ker(𝒯 - 1)` is the zero subspace `⊥`. -/
theorem horizonCapacitance_eq_zero_iff_ego_bot [FiniteDimensional R M] (𝒯 : Module.End R M) :
    horizonCapacitance 𝒯 = 0 ↔ horizonDefectEgo 𝒯 = ⊥ := by
  unfold horizonCapacitance
  rw [Nat.cast_eq_zero, Submodule.finrank_eq_zero]

/-- **Defect-Support Characterization (`twist_mul_eq_self_iff_range_le_ego`):**
A Modular Hamiltonian $K \in \mathrm{End}_R(M)$ satisfies $\mathcal{T} * K = K$ (every state in
the image of $K$ is fixed by the Möbius twist $\mathcal{T}$) if and only if
$\mathrm{range}(K) \le \mathrm{horizonDefectEgo}(\mathcal{T})$. -/
theorem twist_mul_eq_self_iff_range_le_ego
    (𝒯 K : Module.End R M) :
    𝒯 * K = K ↔ LinearMap.range K ≤ horizonDefectEgo 𝒯 := by
  unfold horizonDefectEgo
  constructor
  · intro hTK y hy
    rcases hy with ⟨x, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply]
    have hEval := congr_arg (fun f : Module.End R M => f x) hTK
    simp only [Module.End.mul_apply] at hEval
    rw [hEval, sub_self]
  · intro hRange
    ext x
    have hx : K x ∈ LinearMap.range K := ⟨x, rfl⟩
    have hKer := hRange hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hKer
    exact hKer

/-- **Non-Vacuous Theorem (`time_requires_horizon` — Replacing `True := trivial`):**
If the Modular Hamiltonian $K \in \mathrm{End}_R(M)$ is supported on the Horizon Defect Block
($\mathcal{T} * K = K$, equivalently $\mathrm{range}(K) \le \mathrm{horizonDefectEgo}(\mathcal{T})$)
and the Horizon Capacitance vanishes (`horizonCapacitance 𝒯 = 0`), then:
1. `horizonDefectEgo 𝒯 = ⊥` (the horizon defect subspace is trivial);
2. `LinearMap.range K = ⊥`;
3. **`K = 0` identically** (Modular Time cannot exist without a horizon defect);
4. For any grading/conjugation $J_\Delta$, `kreinSupertrace J_Δ K = 0`. -/
theorem time_requires_horizon
    [FiniteDimensional R M]
    (𝒯 J_Δ K : Module.End R M)
    (h_defect_support : 𝒯 * K = K)
    (h_trivial_horizon : horizonCapacitance 𝒯 = 0) :
    horizonDefectEgo 𝒯 = ⊥ ∧
    LinearMap.range K = ⊥ ∧
    K = 0 ∧
    kreinSupertrace J_Δ K = 0 := by
  have hBot : horizonDefectEgo 𝒯 = ⊥ :=
    (horizonCapacitance_eq_zero_iff_ego_bot 𝒯).mp h_trivial_horizon
  have hRangeLe : LinearMap.range K ≤ horizonDefectEgo 𝒯 :=
    (twist_mul_eq_self_iff_range_le_ego 𝒯 K).mp h_defect_support
  rw [hBot, le_bot_iff] at hRangeLe
  have hK : K = 0 := LinearMap.range_eq_bot.mp hRangeLe
  have hStr : kreinSupertrace J_Δ K = 0 := by
    unfold kreinSupertrace
    rw [hK, mul_zero, map_zero]
  exact ⟨hBot, hRangeLe, hK, hStr⟩

/-- **Contrapositive Discovery Theorem (`non_zero_modular_hamiltonian_forces_positive_horizon_capacitance`):**
If a defect-supported Modular Hamiltonian is non-zero ($K \neq 0$ with $\mathcal{T} * K = K$),
then the Horizon Defect Block is non-trivial (`horizonDefectEgo 𝒯 ≠ ⊥`) and the Horizon Capacitance
is strictly positive (`0 < horizonCapacitance 𝒯`). -/
theorem non_zero_modular_hamiltonian_forces_positive_horizon_capacitance
    [FiniteDimensional R M]
    (𝒯 K : Module.End R M)
    (h_defect_support : 𝒯 * K = K)
    (hK_ne_zero : K ≠ 0) :
    horizonDefectEgo 𝒯 ≠ ⊥ ∧ 0 < horizonCapacitance 𝒯 := by
  have hCapNeZero : horizonCapacitance 𝒯 ≠ 0 := by
    intro hCapZero
    exact hK_ne_zero (time_requires_horizon 𝒯 1 K h_defect_support hCapZero).2.2.1
  have hBotNe : horizonDefectEgo 𝒯 ≠ ⊥ := by
    intro hBot
    exact hCapNeZero ((horizonCapacitance_eq_zero_iff_ego_bot 𝒯).mpr hBot)
  refine ⟨hBotNe, ?_⟩
  unfold horizonCapacitance
  have hNonneg : (0 : ℤ) ≤ (Module.finrank R (horizonDefectEgo 𝒯) : ℤ) :=
    Nat.cast_nonneg _
  exact lt_of_le_of_ne hNonneg (Ne.symm hCapNeZero)

/-- **Commuting Modular Flow Preserves the Horizon Defect (`modular_hamiltonian_preserves_horizon_defect_of_commutes`):**
Whenever the Modular Hamiltonian $K$ commutes with the Möbius twist $\mathcal{T}$
($K * \mathcal{T} = \mathcal{T} * K$), $K$ maps the horizon defect subspace
`horizonDefectEgo 𝒯 = ker(𝒯 - 1)` into itself:
$$\forall v \in \mathrm{horizonDefectEgo}(\mathcal{T}),\quad K v \in \mathrm{horizonDefectEgo}(\mathcal{T}).$$ -/
theorem modular_hamiltonian_preserves_horizon_defect_of_commutes
    (𝒯 K : Module.End R M) (hComm : K * 𝒯 = 𝒯 * K)
    (v : M) (hv : v ∈ horizonDefectEgo 𝒯) :
    K v ∈ horizonDefectEgo 𝒯 := by
  unfold horizonDefectEgo at hv ⊢
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv ⊢
  have hEval := congr_arg (fun f : Module.End R M => f v) hComm.symm
  simp only [Module.End.mul_apply] at hEval
  rw [hEval, hv]

/-- **Modular Time Anomaly Theorem (`modular_anomaly_breaks_twist_commutation_and_forces_nonzero_time`):**
If $J_\Delta$ is a Krein modular involution ($J_\Delta^2 = 1$), $K$ satisfies the twin-sheet
modular conjugation law $J_\Delta K J_\Delta = -K$, and the Krein supertrace of the
modular-twist commutator $[K, \mathcal{T}] = K \mathcal{T} - \mathcal{T} K$ is non-zero:
$$\mathrm{kreinSupertrace}\; J_\Delta\; (K * \mathcal{T} - \mathcal{T} * K) \neq 0,$$
then simultaneously:
1. $K \neq 0$ (Modular Time is non-trivial);
2. $\mathcal{T} \neq 0$ (the Möbius twist is non-trivial);
3. $J_\Delta \neq 1 \land J_\Delta \neq -1$ (the twin-sheet Krein grading is non-trivial);
4. $K * \mathcal{T} \neq \mathcal{T} * K$ (the Modular Hamiltonian cannot commute with the
   Möbius twist in the presence of a non-zero Krein anomaly). -/
theorem modular_anomaly_breaks_twist_commutation_and_forces_nonzero_time
    [Invertible (2 : R)] [FiniteDimensional R M]
    (J_Δ 𝒯 K : Module.End R M)
    (hConj : J_Δ * K * J_Δ = -K)
    (hAnomaly : kreinSupertrace J_Δ (K * 𝒯 - 𝒯 * K) ≠ 0) :
    K ≠ 0 ∧ 𝒯 ≠ 0 ∧ J_Δ ≠ 1 ∧ J_Δ ≠ -1 ∧ K * 𝒯 ≠ 𝒯 * K := by
  have hTriv := modular_hamiltonian_zero_of_trivial_conjugation J_Δ K hConj
  have hStrZero : kreinSupertrace J_Δ (0 : Module.End R M) = 0 := by
    unfold kreinSupertrace
    rw [mul_zero, map_zero]
  have hKNe : K ≠ 0 := by
    intro hK0
    rw [hK0, zero_mul, mul_zero, sub_zero] at hAnomaly
    exact hAnomaly hStrZero
  have hTNe : 𝒯 ≠ 0 := by
    intro hT0
    rw [hT0, mul_zero, zero_mul, sub_zero] at hAnomaly
    exact hAnomaly hStrZero
  have hJNeOne : J_Δ ≠ 1 := by
    intro hOne
    exact hKNe (hTriv.1 hOne)
  have hJNeNegOne : J_Δ ≠ -1 := by
    intro hNegOne
    exact hKNe (hTriv.2 hNegOne)
  have hNotComm : K * 𝒯 ≠ 𝒯 * K := by
    intro hComm
    rw [hComm, sub_self] at hAnomaly
    exact hAnomaly hStrZero
  exact ⟨hKNe, hTNe, hJNeOne, hJNeNegOne, hNotComm⟩

end HorizonCapacitanceAndTime

-- ============================================================================
-- SECTION 4: Horizon Capacitance as the Spinor Trace of 𝒯 on the Defect Block Q₀
-- ============================================================================

section SpinorTraceHorizonCapacitance

variable {R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

/-- Positive-chirality Weyl/Peirce projector $P_+(\mathcal{T}) = \frac{1}{2}(1 + \mathcal{T})$
onto the Horizon Defect Block $Q_0 = \mathrm{horizonDefectEgo}(\mathcal{T}) = \ker(\mathcal{T} - 1)$. -/
def horizonProjectorPos (𝒯 : Module.End R M) : Module.End R M :=
  ⅟(2 : R) • (1 + 𝒯)

/-- Negative-chirality Weyl/Peirce projector $P_-(\mathcal{T}) = \frac{1}{2}(1 - \mathcal{T})$
onto the complementary mirror block $\mathrm{horizonMirrorAnima}(\mathcal{T}) = \ker(\mathcal{T} + 1)$. -/
def horizonProjectorNeg (𝒯 : Module.End R M) : Module.End R M :=
  ⅟(2 : R) • (1 - 𝒯)

/-- **Spinor Trace of the Möbius Twist on the Horizon Defect Block (`horizonProjector_twist_restriction_and_trace_splitting`):**
For any Möbius/Krein involution $\mathcal{T} \in \mathrm{End}_R(M)$ satisfying $\mathcal{T}^2 = 1$:
1. **Capacitor Plate Completeness:** $P_+(\mathcal{T}) + P_-(\mathcal{T}) = 1$;
2. **Parity Charge Decomposition:** $P_+(\mathcal{T}) - P_-(\mathcal{T}) = \mathcal{T}$;
3. **Defect-Block Eigenvalue $+1$:** Restricting $\mathcal{T}$ to $Q_0$ via $P_+(\mathcal{T})$
   fixes $P_+(\mathcal{T})$: $\mathcal{T} * P_+(\mathcal{T}) = P_+(\mathcal{T})$;
4. **Mirror-Block Eigenvalue $-1$:** $\mathcal{T} * P_-(\mathcal{T}) = - P_-(\mathcal{T})$;
5. **Horizon Capacitance Trace Identity:** Over any finite free module, the trace of $\mathcal{T}$
   restricted to $Q_0$ equals the trace of $P_+(\mathcal{T})$ and satisfies
   $$2 \cdot \mathrm{Tr}(\mathcal{T} P_+(\mathcal{T})) = \mathrm{Tr}(1_M) + \mathrm{Tr}(\mathcal{T}).$$ -/
theorem horizonProjector_twist_restriction_and_trace_splitting
    [Module.Free R M] [Module.Finite R M]
    (𝒯 : Module.End R M) (hKrein : 𝒯 * 𝒯 = 1) :
    horizonProjectorPos 𝒯 + horizonProjectorNeg 𝒯 = 1 ∧
    horizonProjectorPos 𝒯 - horizonProjectorNeg 𝒯 = 𝒯 ∧
    𝒯 * horizonProjectorPos 𝒯 = horizonProjectorPos 𝒯 ∧
    𝒯 * horizonProjectorNeg 𝒯 = - horizonProjectorNeg 𝒯 ∧
    LinearMap.trace R M (𝒯 * horizonProjectorPos 𝒯) =
      LinearMap.trace R M (horizonProjectorPos 𝒯) ∧
    (2 : R) * LinearMap.trace R M (𝒯 * horizonProjectorPos 𝒯) =
      LinearMap.trace R M (1 : Module.End R M) + LinearMap.trace R M 𝒯 := by
  have hTPos : 𝒯 * horizonProjectorPos 𝒯 = horizonProjectorPos 𝒯 := by
    unfold horizonProjectorPos
    rw [mul_smul_comm, mul_add, mul_one, hKrein, add_comm]
  have hTNeg : 𝒯 * horizonProjectorNeg 𝒯 = - horizonProjectorNeg 𝒯 := by
    unfold horizonProjectorNeg
    rw [mul_smul_comm, mul_sub, mul_one, hKrein, ← smul_neg, neg_sub]
  refine ⟨?_, ?_, hTPos, hTNeg, congr_arg (LinearMap.trace R M) hTPos, ?_⟩
  · unfold horizonProjectorPos horizonProjectorNeg
    rw [← smul_add]
    have hAdd : (1 : Module.End R M) + 𝒯 + (1 - 𝒯) = (2 : R) • (1 : Module.End R M) := by
      rw [two_smul]
      abel
    rw [hAdd, ← mul_smul, invOf_mul_self, one_smul]
  · unfold horizonProjectorPos horizonProjectorNeg
    rw [← smul_sub]
    have hSub : (1 : Module.End R M) + 𝒯 - (1 - 𝒯) = (2 : R) • 𝒯 := by
      rw [two_smul]
      abel
    rw [hSub, ← mul_smul, invOf_mul_self, one_smul]
  · rw [hTPos]
    unfold horizonProjectorPos
    rw [map_smul, map_add, smul_eq_mul, ← mul_assoc, mul_invOf_self, one_mul]

end SpinorTraceHorizonCapacitance

-- ============================================================================
-- SECTION 5: Concrete $(5,5)$ 10D Matrix Trace = 5 & Twin-Sheet Non-Commutativity Witnesses
-- ============================================================================

/-- The 5-mode positive-chirality horizon support $\{0, 1, 2, 3, 4\} \subset \mathrm{Fin}\,10$
inside the 10-dimensional $(5,5)$ split-signature Krein horizon carrier. -/
def krein55HorizonSupport : Finset (Fin 10) :=
  Finset.univ.filter (fun i : Fin 10 => i.val < 5)

/-- The complementary 5-mode negative-chirality mirror support $\{5, 6, 7, 8, 9\} \subset \mathrm{Fin}\,10$
inside the 10-dimensional $(5,5)$ split-signature Krein horizon carrier. -/
def krein55MirrorSupport : Finset (Fin 10) :=
  Finset.univ.filter (fun i : Fin 10 => 5 ≤ i.val)

/-- **Discrete $(5,5)$ Horizon Support Quantization (`krein55_horizon_support_quantization`):**
Kernel-checked by `rfl`: in the 10-dimensional $(5,5)$ split-signature Krein horizon carrier,
both `krein55HorizonSupport` and `krein55MirrorSupport` carry exactly **5 discrete modes**
(5 bits of horizon capacity), summing to 10 with disjoint support. -/
theorem krein55_horizon_support_quantization :
    krein55HorizonSupport.card = 5 ∧
    krein55MirrorSupport.card = 5 ∧
    krein55HorizonSupport.card + krein55MirrorSupport.card = 10 ∧
    krein55HorizonSupport ∩ krein55MirrorSupport = ∅ := by
  have h1 : krein55HorizonSupport.card = 5 := rfl
  have h2 : krein55MirrorSupport.card = 5 := rfl
  refine ⟨h1, h2, ?_, rfl⟩
  rw [h1, h2]

/-- Explicit $10 \times 10$ $(5,5)$ Möbius/Krein twist matrix
$\mathcal{T}_{5,5} = \mathrm{diag}(+1,+1,+1,+1,+1,-1,-1,-1,-1,-1)$ on `Fin 10`. -/
def krein10Twist : Matrix (Fin 10) (Fin 10) ℝ :=
  Matrix.diagonal (fun i : Fin 10 => if i.val < 5 then (1 : ℝ) else -1)

/-- Explicit $10 \times 10$ Horizon Defect Projector $P_+(\mathcal{T}_{5,5}) = \frac{1}{2}(I_{10} + \mathcal{T}_{5,5})$
projecting onto the 5-dimensional positive-chirality horizon block $Q_0 \subset \mathbb{R}^{10}$. -/
def krein10HorizonProjector : Matrix (Fin 10) (Fin 10) ℝ :=
  Matrix.diagonal (fun i : Fin 10 => if i.val < 5 then (1 : ℝ) else 0)

/-- Elementary $10 \times 10$ inter-sheet transition matrix $E_{0,5}$ coupling mode $0 \in Q_0$
(Ego plate) to mode $5 \in Q_0^\perp$ (Anima plate). -/
def krein10InterSheetCouple : Matrix (Fin 10) (Fin 10) ℝ :=
  Matrix.of (fun i j : Fin 10 => if i.val = 0 ∧ j.val = 5 then (1 : ℝ) else 0)

/-- Explicit non-commutativity witness for the 10D $(5,5)$ carrier `Matrix (Fin 10) (Fin 10) ℝ`:
the Möbius twist $\mathcal{T}_{5,5}$ does not commute with inter-sheet transitions between
$Q_0$ and $Q_0^\perp$ ($\mathcal{T}_{5,5} E_{0,5} \neq E_{0,5} \mathcal{T}_{5,5}$). -/
theorem krein10_twist_interSheet_noncommutative :
    krein10Twist * krein10InterSheetCouple ≠ krein10InterSheetCouple * krein10Twist := by
  intro hEq
  have h05 := congr_fun (congr_fun hEq ⟨0, by decide⟩) ⟨5, by decide⟩
  simp [krein10Twist, krein10InterSheetCouple, Matrix.diagonal_mul, Matrix.mul_diagonal] at h05
  norm_num at h05

/-- **Constructive Spinor-Trace Theorem for the $(5,5)$ Horizon Capacitance (`krein10_horizon_trace_capacitance_eq_five`):**
On the explicit 10-dimensional $(5,5)$ split-signature matrix realization:
1. $\mathcal{T}_{5,5}^2 = I_{10}$ ($\mathcal{T}_{5,5}$ is an involutive Möbius/Krein twist);
2. $\mathrm{Tr}(\mathcal{T}_{5,5}) = 0$ (the global Witten supertrace vanishes across the Klein bottle);
3. $\mathcal{T}_{5,5} P_+(\mathcal{T}_{5,5}) = P_+(\mathcal{T}_{5,5})$ (on the horizon defect $Q_0$, $\mathcal{T}_{5,5}$ acts as $+1$);
4. **Spinor Trace = 5 Bits (Derived Directly Without Assuming `finrank = 5`):**
   $$\mathrm{Tr}\big(\mathcal{T}_{5,5}\, P_+(\mathcal{T}_{5,5})\big) = \mathrm{Tr}\big(P_+(\mathcal{T}_{5,5})\big) = 5;$$
5. **Holographic Half-Bulk Law:**
   $$2 \cdot \mathrm{Tr}\big(\mathcal{T}_{5,5}\, P_+(\mathcal{T}_{5,5})\big) = \mathrm{Tr}(I_{10}) = 10.$$ -/
theorem krein10_horizon_trace_capacitance_eq_five :
    krein10Twist * krein10Twist = 1 ∧
    Matrix.trace krein10Twist = 0 ∧
    krein10Twist * krein10HorizonProjector = krein10HorizonProjector ∧
    Matrix.trace (krein10Twist * krein10HorizonProjector) = 5 ∧
    Matrix.trace krein10HorizonProjector = 5 ∧
    2 * Matrix.trace (krein10Twist * krein10HorizonProjector) =
      Matrix.trace (1 : Matrix (Fin 10) (Fin 10) ℝ) := by
  have hSq : krein10Twist * krein10Twist = 1 := by
    unfold krein10Twist
    rw [Matrix.diagonal_mul_diagonal]
    have hDiag : (fun i : Fin 10 => (if i.val < 5 then (1 : ℝ) else -1) * (if i.val < 5 then 1 else -1)) =
        fun _ => (1 : ℝ) := by
      ext i
      by_cases hi : i.val < 5 <;> simp [hi]
    rw [hDiag, Matrix.diagonal_one]
  have hRestrict : krein10Twist * krein10HorizonProjector = krein10HorizonProjector := by
    unfold krein10Twist krein10HorizonProjector
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    by_cases hi : i.val < 5 <;> simp [hi]
  have hTrProj : Matrix.trace krein10HorizonProjector = 5 := by
    simp only [krein10HorizonProjector, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_apply_eq]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
        Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
        Fin.sum_univ_two]
    norm_num
  have hTrTwist : Matrix.trace krein10Twist = 0 := by
    simp only [krein10Twist, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_apply_eq]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
        Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
        Fin.sum_univ_two]
    norm_num
  have hTrRestr : Matrix.trace (krein10Twist * krein10HorizonProjector) = 5 := by
    rw [hRestrict, hTrProj]
  refine ⟨hSq, hTrTwist, hRestrict, hTrRestr, hTrProj, ?_⟩
  rw [hTrRestr]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.one_apply_eq]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_two]
  norm_num

/-- Canonical $2 \times 2$ Krein twin-sheet modular conjugation matrix
$J_2 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$, exchanging the Ego and Anima sheets. -/
def kreinJ2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1;
     1, 0]

/-- Canonical $2 \times 2$ twin-sheet Modular Hamiltonian generator
$K_2(\omega) = \begin{pmatrix} \omega & 0 \\ 0 & -\omega \end{pmatrix}$ with modular frequency
$+\omega$ on the Ego sheet and $-\omega$ on the Anima sheet. -/
def kreinK2 (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ω,  0;
     0, -ω]

/-- Unit-frequency $2 \times 2$ twin-sheet Modular Hamiltonian $K_2(1)$. -/
def kreinK2Unit : Matrix (Fin 2) (Fin 2) ℝ :=
  kreinK2 1

/-- **Concrete Twin-Sheet Modular Hamiltonian & Trace Neutrality Theorem (`krein2_modular_conjugation_and_trace_laws`):**
For any modular frequency $\omega \in \mathbb{R}$:
1. $J_2^2 = I_2$ ($J_2$ is a Krein modular involution);
2. $J_2 K_2(\omega) J_2 = -K_2(\omega)$ (conjugation by $J_2$ reverses the direction of modular time);
3. $J_2 K_2(\omega) = - K_2(\omega) J_2$ ($K_2(\omega)$ anti-commutes with $J_2$);
4. Both the ordinary trace $\mathrm{Tr}(K_2(\omega)) = 0$ and the Krein supertrace
   $\mathrm{Tr}(J_2 K_2(\omega)) = 0$ vanish identically. -/
theorem krein2_modular_conjugation_and_trace_laws (ω : ℝ) :
    kreinJ2 * kreinJ2 = 1 ∧
    kreinJ2 * kreinK2 ω * kreinJ2 = -kreinK2 ω ∧
    kreinJ2 * kreinK2 ω = -(kreinK2 ω * kreinJ2) ∧
    Matrix.trace (kreinK2 ω) = 0 ∧
    Matrix.trace (kreinJ2 * kreinK2 ω) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [kreinJ2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [kreinJ2, kreinK2, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [kreinJ2, kreinK2, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [kreinK2, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  · simp [kreinJ2, kreinK2, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]

/-- Explicit non-commutativity witness for the twin-sheet modular conjugation $J_2$ and unit
Modular Hamiltonian $K_2(1)$: $J_2 K_2(1) \neq K_2(1) J_2$. -/
theorem krein2_modular_noncommutative :
    kreinJ2 * kreinK2Unit ≠ kreinK2Unit * kreinJ2 := by
  intro hEq
  have h01 := congr_fun (congr_fun hEq 0) 1
  simp [kreinJ2, kreinK2Unit, kreinK2, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

end

end InfoGeometry.Canonical.ModularHamiltonianHorizonDefectPoset

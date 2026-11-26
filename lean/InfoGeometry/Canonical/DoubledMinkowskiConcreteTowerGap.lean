/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge

/-!
# Concrete finite-stage tower for doubled-Minkowski BdG gap persistence

This module instantiates the abstract directed-tower theorem of
`DoubledMinkowskiBdGColimitBridge` with a concrete refinement of doubled BdG
state spaces by padding one zero particle/hole component per stage. It proves
that Euclidean norm and sheet-Krein pairing are preserved, that the zero-kinetic
BdG quadratic form is exactly `m² * ‖ψ‖²`, and that the abstract colimit theorem
therefore yields a projective limit quadratic form with the same lower bound.
A finite-support nonzero step-error perturbation is also included so the
summable-error hypothesis is exercised non-trivially.

No continuum 4D Yang–Mills existence, Wightman/OS axioms, or physical spectral
mass-gap theorem is claimed.
-/

namespace InfoGeometry.Canonical.DoubledMinkowskiConcreteTowerGap

open InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge
open scoped BigOperators
open Filter

/-- Non-commutativity witness inherited from the concrete BdG block carrier. -/
theorem concreteTower_noncommWitness :
    ∃ A B : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ, A * B ≠ B * A :=
  exists_noncomm_bdg_mat

/-- Pad a finite vector by one zero component at the last index. -/
def pad {n : ℕ} (u : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.lastCases 0 u

/-- Lift the padding to a doubled particle/hole state. -/
def padSum {n : ℕ} (ψ : Fin n ⊕ Fin n → ℝ) : Fin (n + 1) ⊕ Fin (n + 1) → ℝ :=
  Sum.elim (fun i => pad (fun j => ψ (Sum.inl j)) i)
           (fun i => pad (fun j => ψ (Sum.inr j)) i)

/-- Padding preserves the Euclidean dot product. -/
theorem pad_dotProduct {n : ℕ} (u v : Fin n → ℝ) :
    dotProduct (pad u) (pad v) = dotProduct u v := by
  simp [dotProduct, pad, Fin.sum_univ_castSucc]

/-- Padding preserves the doubled-state dot product. -/
theorem padSum_dotProduct {n : ℕ} (ψ φ : Fin n ⊕ Fin n → ℝ) :
    dotProduct (padSum ψ) (padSum φ) = dotProduct ψ φ := by
  simp [dotProduct, padSum, pad, Fin.sum_univ_castSucc, Fintype.sum_sum_type]

/-- Sheet Krein involution `diag(1, -1)` on a finite BdG stage. -/
def sheetKrein (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- Sheet-Krein pairing on a finite BdG stage. -/
def bdgKreinPair {n : ℕ} (ψ φ : Fin n ⊕ Fin n → ℝ) : ℝ :=
  dotProduct ψ ((sheetKrein n).mulVec φ)

/-- Padding preserves the sheet-Krein pairing. -/
theorem padSum_bdgKreinPair {n : ℕ} (ψ φ : Fin n ⊕ Fin n → ℝ) :
    bdgKreinPair (padSum ψ) (padSum φ) = bdgKreinPair ψ φ := by
  simp [bdgKreinPair, sheetKrein, Matrix.mulVec, Matrix.one_apply, dotProduct,
    padSum, pad, Fin.sum_univ_castSucc, Fintype.sum_sum_type]

/-- BdG quadratic form for the zero-kinetic stage with pairing gap `m`. -/
def stageBdgQuad {n : ℕ} (m : ℝ) (ψ : Fin n ⊕ Fin n → ℝ) : ℝ :=
  let H := bdgHamiltonian (0 : Matrix (Fin n) (Fin n) ℝ) m
  dotProduct ψ ((H * H).mulVec ψ)

/-- The zero-kinetic BdG quadratic form is exactly `m² * ‖ψ‖²`. -/
theorem stageBdgQuad_eq {n : ℕ} (m : ℝ) (ψ : Fin n ⊕ Fin n → ℝ) :
    stageBdgQuad m ψ = m ^ 2 * dotProduct ψ ψ := by
  have h := bdg_gapped_spectrum_and_particle_hole_symmetry
    (0 : Matrix (Fin n) (Fin n) ℝ) (by simp) m ψ
  dsimp [stageBdgQuad]
  rw [h.2.2.1]
  simp [Matrix.mulVec, Matrix.one_apply, dotProduct, Fintype.sum_sum_type,
    mul_add, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Uniform gap bound at every concrete finite stage. -/
theorem stageBdgQuad_gap {n : ℕ} (m : ℝ) (ψ : Fin n ⊕ Fin n → ℝ) :
    m ^ 2 * dotProduct ψ ψ ≤ stageBdgQuad m ψ := by
  rw [stageBdgQuad_eq]

/-- The concrete BdG quadratic form is invariant under stage padding. -/
theorem stageBdgQuad_pad {n : ℕ} (m : ℝ) (ψ : Fin n ⊕ Fin n → ℝ) :
    stageBdgQuad m (padSum ψ) = stageBdgQuad m ψ := by
  rw [stageBdgQuad_eq, stageBdgQuad_eq, padSum_dotProduct]

/-- Euclidean norm is strictly invariant along the concrete padding tower. -/
theorem seqVal_normSq_pad :
    ∀ n (ψ : Fin n ⊕ Fin n → ℝ) (k : ℕ),
      seqVal (fun n => padSum (n := n)) (fun n ψ => dotProduct ψ ψ) n ψ k =
        dotProduct ψ ψ := by
  intro n ψ k
  induction k generalizing n ψ with
  | zero => rfl
  | succ k ih =>
    change seqVal (fun n => padSum (n := n)) (fun n ψ => dotProduct ψ ψ) (n + 1)
      (padSum ψ) k = dotProduct ψ ψ
    rw [ih, padSum_dotProduct]

/-- Concrete instance of the abstract doubled-Minkowski BdG colimit gap theorem.
The resulting `Q_inf` is a projective limit quadratic form with the same
`m²`-lower bound; it is not a continuum Yang–Mills measure. -/
theorem concrete_tower_gap (m : ℝ) :
    ∃ Q_inf : (n : ℕ) → (Fin n ⊕ Fin n → ℝ) → ℝ,
      (∀ n (ψ : Fin n ⊕ Fin n → ℝ),
        Tendsto (seqVal (fun n => padSum (n := n)) (fun n ψ => stageBdgQuad m ψ) n ψ) atTop
          (nhds (Q_inf n ψ))) ∧
      (∀ n (ψ : Fin n ⊕ Fin n → ℝ),
        m ^ 2 * dotProduct ψ ψ ≤ Q_inf n ψ) := by
  have h := continuum_colimit_doubled_minkowski_and_bdg_mass_gap
    (V := fun n => Fin n ⊕ Fin n → ℝ)
    (ι := fun n => padSum (n := n))
    (normSq := fun n ψ => dotProduct ψ ψ)
    (kreinPair := fun n ψ φ => bdgKreinPair ψ φ)
    (bdgQuad := fun n ψ => stageBdgQuad m ψ)
    (ε := fun _ => 0) m
    (by intro n ψ; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (ψ i))
    (by intro n ψ; exact padSum_dotProduct ψ ψ)
    (by intro n ψ φ; exact padSum_bdgKreinPair ψ φ)
    (by intro n ψ; exact stageBdgQuad_gap m ψ)
    (by simp)
    (by intro n ψ; simp [stageBdgQuad_pad])
  rcases h with ⟨hKrein, Q_inf, hTendsto, hProj, hGap, hNN⟩
  exact ⟨Q_inf, hTendsto, hGap⟩

/-- The BdG quadratic sequence is exactly constant along the concrete tower. -/
theorem seqVal_stageBdgQuad_pad (m : ℝ) :
    ∀ n (ψ : Fin n ⊕ Fin n → ℝ) (k : ℕ),
      seqVal (fun n => padSum (n := n)) (fun n ψ => stageBdgQuad m ψ) n ψ k =
        m ^ 2 * dotProduct ψ ψ := by
  intro n ψ k
  induction k generalizing n ψ with
  | zero => simp [seqVal, stageBdgQuad_eq]
  | succ k ih =>
    change seqVal (fun n => padSum (n := n)) (fun n ψ => stageBdgQuad m ψ) (n + 1)
      (padSum ψ) k = m ^ 2 * dotProduct ψ ψ
    rw [ih, padSum_dotProduct]

/-- Stronger concrete limit: the colimit quadratic form is explicitly
`m²‖ψ‖²`, not merely an unspecified gap-preserving limit. -/
theorem concrete_tower_explicit_Qinf (m : ℝ) :
    ∃ Q_inf : (n : ℕ) → (Fin n ⊕ Fin n → ℝ) → ℝ,
      (∀ n (ψ : Fin n ⊕ Fin n → ℝ),
        Tendsto (seqVal (fun n => padSum (n := n)) (fun n ψ => stageBdgQuad m ψ) n ψ) atTop
          (nhds (Q_inf n ψ))) ∧
      (∀ n (ψ : Fin n ⊕ Fin n → ℝ),
        m ^ 2 * dotProduct ψ ψ ≤ Q_inf n ψ) ∧
      (∀ n (ψ : Fin n ⊕ Fin n → ℝ),
        Q_inf n ψ = m ^ 2 * dotProduct ψ ψ) := by
  refine ⟨fun n ψ => m ^ 2 * dotProduct ψ ψ, ?_, ?_, ?_⟩
  · intro n ψ
    have hfun : seqVal (fun n => padSum (n := n))
        (fun n ψ => stageBdgQuad m ψ) n ψ =
        (fun _ => m ^ 2 * dotProduct ψ ψ) := by
      funext k
      exact seqVal_stageBdgQuad_pad m n ψ k
    rw [hfun]
    exact tendsto_const_nhds
  · intro n ψ
    rfl
  · intro n ψ
    rfl

/-- Single nonzero step error at stage zero; finite support makes it summable. -/
def perturbEps : ℕ → ℝ := fun n => if n = 0 then 1 else 0

/-- Matching finite-support perturbation of the BdG quadratic coefficient. -/
def perturbCoeff : ℕ → ℝ := fun n => if n = 0 then 1 else 0

/-- BdG quadratic form with a finite-support perturbation at the first stage. -/
def perturbedQuad (m : ℝ) (n : ℕ) (ψ : Fin n ⊕ Fin n → ℝ) : ℝ :=
  (m ^ 2 + perturbCoeff n) * dotProduct ψ ψ

theorem perturbEps_summable : Summable perturbEps := by
  refine summable_of_ne_finset_zero (s := {0}) ?_
  intro b hb
  simp [perturbEps]
  exact by simpa using hb

theorem perturbCoeff_nonneg (n : ℕ) : 0 ≤ perturbCoeff n := by
  by_cases h : n = 0 <;> simp [perturbCoeff, h]

/-- The perturbed form still dominates `m²‖ψ‖²`. -/
theorem perturbedQuad_gap (m : ℝ) :
    ∀ n (ψ : Fin n ⊕ Fin n → ℝ), m ^ 2 * dotProduct ψ ψ ≤ perturbedQuad m n ψ := by
  intro n ψ
  have hnn : 0 ≤ dotProduct ψ ψ :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (ψ i)
  have hc : 0 ≤ perturbCoeff n * dotProduct ψ ψ :=
    mul_nonneg (perturbCoeff_nonneg n) hnn
  dsimp [perturbedQuad]
  nlinarith

/-- The step error is nonzero only at stage zero and is dominated by `ε₀`. -/
theorem perturbedQuad_step (m : ℝ) :
    ∀ n (ψ : Fin n ⊕ Fin n → ℝ),
      |perturbedQuad m (n + 1) (padSum ψ) - perturbedQuad m n ψ| ≤
        perturbEps n * dotProduct ψ ψ := by
  intro n ψ
  dsimp [perturbedQuad]
  rw [padSum_dotProduct]
  by_cases hn : n = 0
  · subst n
    simp [perturbedQuad, perturbCoeff, perturbEps]
  · simp [hn, perturbedQuad, perturbCoeff, perturbEps]

/-- Nonzero-error instance: a summable finite-support perturbation preserves
the uniform BdG gap through the abstract colimit theorem. -/
theorem perturbed_tower_gap (m : ℝ) :
    ∃ Q_inf : (n : ℕ) → (Fin n ⊕ Fin n → ℝ) → ℝ,
      (∀ n (ψ : Fin n ⊕ Fin n → ℝ),
        Tendsto (seqVal (fun n => padSum (n := n)) (fun n ψ => perturbedQuad m n ψ) n ψ) atTop
          (nhds (Q_inf n ψ))) ∧
      (∀ n (ψ : Fin n ⊕ Fin n → ℝ),
        m ^ 2 * dotProduct ψ ψ ≤ Q_inf n ψ) := by
  have h := continuum_colimit_doubled_minkowski_and_bdg_mass_gap
    (V := fun n => Fin n ⊕ Fin n → ℝ)
    (ι := fun n => padSum (n := n))
    (normSq := fun n ψ => dotProduct ψ ψ)
    (kreinPair := fun n ψ φ => bdgKreinPair ψ φ)
    (bdgQuad := fun n ψ => perturbedQuad m n ψ)
    (ε := perturbEps) m
    (by intro n ψ; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (ψ i))
    (by intro n ψ; exact padSum_dotProduct ψ ψ)
    (by intro n ψ φ; exact padSum_bdgKreinPair ψ φ)
    (perturbedQuad_gap m)
    perturbEps_summable
    (perturbedQuad_step m)
  rcases h with ⟨hKrein, Q_inf, hTendsto, hProj, hGap, hNN⟩
  exact ⟨Q_inf, hTendsto, hGap⟩

/-- After the first refinement stage the finite-support perturbation vanishes. -/
theorem perturbedQuad_eq_of_ne_zero (m : ℝ) {n : ℕ} (hn : n ≠ 0)
    (ψ : Fin n ⊕ Fin n → ℝ) :
    perturbedQuad m n ψ = m ^ 2 * dotProduct ψ ψ := by
  simp [perturbedQuad, perturbCoeff, hn]

/-- The perturbed sequence is exactly constant from stage one onward. -/
theorem seqVal_perturbed_after_first (m : ℝ) :
    ∀ n (ψ : Fin (n + 1) ⊕ Fin (n + 1) → ℝ) (k : ℕ),
      seqVal (fun n => padSum (n := n)) (fun n ψ => perturbedQuad m n ψ) (n + 1) ψ k =
        m ^ 2 * dotProduct ψ ψ := by
  intro n ψ k
  induction k generalizing n ψ with
  | zero =>
    simp [seqVal, perturbedQuad_eq_of_ne_zero m (Nat.succ_ne_zero n)]
  | succ k ih =>
    change seqVal (fun n => padSum (n := n)) (fun n ψ => perturbedQuad m n ψ)
      ((n + 1) + 1) (padSum ψ) k = m ^ 2 * dotProduct ψ ψ
    rw [ih, padSum_dotProduct]

/-- Nonzero-error tower with an explicitly washed-out limit: the single
stage-zero perturbation disappears and `Q_inf = m²‖ψ‖²`. -/
theorem perturbed_tower_explicit_Qinf (m : ℝ) :
    ∃ Q_inf : (n : ℕ) → (Fin n ⊕ Fin n → ℝ) → ℝ,
      (∀ n (ψ : Fin n ⊕ Fin n → ℝ),
        Tendsto (seqVal (fun n => padSum (n := n)) (fun n ψ => perturbedQuad m n ψ) n ψ) atTop
          (nhds (Q_inf n ψ))) ∧
      (∀ n (ψ : Fin n ⊕ Fin n → ℝ),
        m ^ 2 * dotProduct ψ ψ ≤ Q_inf n ψ) ∧
      (∀ n (ψ : Fin n ⊕ Fin n → ℝ),
        Q_inf n ψ = m ^ 2 * dotProduct ψ ψ) := by
  refine ⟨fun n ψ => m ^ 2 * dotProduct ψ ψ, ?_, ?_, ?_⟩
  · intro n ψ
    apply (tendsto_add_atTop_iff_nat 1).mp
    have htail : (fun k => seqVal (fun n => padSum (n := n))
        (fun n ψ => perturbedQuad m n ψ) n ψ (k + 1)) =
        (fun _ => m ^ 2 * dotProduct ψ ψ) := by
      funext k
      have h := seqVal_perturbed_after_first m n (padSum ψ) k
      rw [padSum_dotProduct] at h
      exact h
    rw [htail]
    exact tendsto_const_nhds
  · intro n ψ
    exact le_rfl
  · intro n ψ
    rfl

/-- Full nonzero-error instance: the abstract colimit theorem's Krein
invariance, projective compatibility, gap and non-negativity conclusions are
all available for the finite-support perturbation. -/
theorem perturbed_tower_full_instance (m : ℝ) :
    (∀ n (ψ φ : Fin n ⊕ Fin n → ℝ) (k : ℕ),
      seqPair (fun n => padSum (n := n))
        (fun n ψ φ => bdgKreinPair ψ φ) n ψ φ k = bdgKreinPair ψ φ) ∧
    ∃ Q_inf : (n : ℕ) → (Fin n ⊕ Fin n → ℝ) → ℝ,
      (∀ n (ψ : Fin n ⊕ Fin n → ℝ),
        Tendsto (seqVal (fun n => padSum (n := n)) (fun n ψ => perturbedQuad m n ψ) n ψ) atTop
          (nhds (Q_inf n ψ))) ∧
      (∀ n (ψ : Fin n ⊕ Fin n → ℝ),
        Q_inf (n + 1) (padSum ψ) = Q_inf n ψ) ∧
      (∀ n (ψ : Fin n ⊕ Fin n → ℝ),
        m ^ 2 * dotProduct ψ ψ ≤ Q_inf n ψ) ∧
      (∀ n (ψ : Fin n ⊕ Fin n → ℝ),
        0 ≤ Q_inf n ψ) := by
  exact continuum_colimit_doubled_minkowski_and_bdg_mass_gap
    (V := fun n => Fin n ⊕ Fin n → ℝ)
    (ι := fun n => padSum (n := n))
    (normSq := fun n ψ => dotProduct ψ ψ)
    (kreinPair := fun n ψ φ => bdgKreinPair ψ φ)
    (bdgQuad := fun n ψ => perturbedQuad m n ψ)
    (ε := perturbEps) m
    (by intro n ψ; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (ψ i))
    (by intro n ψ; exact padSum_dotProduct ψ ψ)
    (by intro n ψ φ; exact padSum_bdgKreinPair ψ φ)
    (perturbedQuad_gap m)
    perturbEps_summable
    (perturbedQuad_step m)

/-- Linear map form of the single-component padding. -/
def padLinear {n : ℕ} : (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun := pad
  map_add' u v := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [pad]
    · simp [pad]
  map_smul' a u := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [pad]
    · simp [pad]

/-- Linear map form of the doubled-state padding. -/
def padSumLinear {n : ℕ} :
    (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin (n + 1) ⊕ Fin (n + 1) → ℝ) where
  toFun := padSum
  map_add' ψ φ := by
    funext i
    cases i with
    | inl i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [padSum, pad]
      · simp [padSum, pad]
    | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [padSum, pad]
      · simp [padSum, pad]
  map_smul' a ψ := by
    funext i
    cases i with
    | inl i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [padSum, pad]
      · simp [padSum, pad]
    | inr i =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [padSum, pad]
      · simp [padSum, pad]

/-- The linear padding map agrees pointwise with the tower transition. -/
theorem padSumLinear_apply {n : ℕ} (ψ : Fin n ⊕ Fin n → ℝ) :
    padSumLinear ψ = padSum ψ := rfl

end InfoGeometry.Canonical.DoubledMinkowskiConcreteTowerGap

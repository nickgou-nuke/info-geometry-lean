/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.NoncommutativeWeilCohomologyAndPicardLefschetzSynthesis

/-!
# Finite-Stage Bott Tower Identities ($\mathcal{E}_1$–$\mathcal{E}_4$)

These are identities in the recursively defined finite matrix stages
`ClTower A n`, over a noncommutative ring `[Ring A]` and, where needed,
`[StarRing A]`. They do not construct an inverse-limit state space or establish
an analytic infinite-volume or unbounded-operator result:

1. **$\mathcal{E}_1$** (`bott_trace_and_supertrace_cancellation`):
   Unital bulk diagonal doubling `towerTrace (diagEmbed Y_bulk) = 2 • towerTrace Y_bulk`
   versus Bott corner stabilization `towerTrace (bottEmbed X_loc) = towerTrace X_loc`
   and cancellation of the diagonal summand under the supertrace
   `superTrace (bottEmbed X_loc + diagEmbed Y_bulk) = superTrace X_loc`.
2. **$\mathcal{E}_2$** (`finite_stage_observable_state_pairing`):
   Finite-stage trace and supertrace pairing identities for Bott and diagonal
   embeddings of observables with the corresponding block state readouts
   (`irStatePullback`, `rgStatePullback`, `chiralStatePullback`).
3. **$\mathcal{E}_3$** (`bott_iter_preserves_ring_and_hodge_relations`):
   Finite `k`-step homomorphic transport via `bottEmbedIter k` of Lie brackets,
   self-adjoint idempotents with invariant tower trace, and square-zero Hodge relations.
4. **$\mathcal{E}_4$** (`mass_gap_bott_iter_stability`):
   `Nat`-iterated stage stability for the spectral mass-gap operator
   `massGapOp m₀ (n + k) * bottEmbedIter k Ψ = bottEmbedIter k (massGapOp m₀ n * Ψ)`.
-/

open Matrix
open InfoGeometry.Algebra.NoncommutativeHodgeParabolicTowerSynthesis
open InfoGeometry.Algebra.NoncommutativeWeilCohomologyAndPicardLefschetzSynthesis

namespace InfoGeometry.Algebra.NoncommutativeColimitExtensionMechanisms

universe u

section Helpers

variable {A : Type u} [Ring A]

private lemma towerTrace_sub {n : ℕ} (X Y : ClTower A n) :
    towerTrace (X - Y) = towerTrace X - towerTrace Y := by
  rw [sub_eq_add_neg, towerTrace_add, towerTrace_neg, ← sub_eq_add_neg]

omit [Ring A] in
private lemma clTower_nontrivial [Nontrivial A] (n : ℕ) : Nontrivial (ClTower A n) := by
  induction n with
  | zero => infer_instance
  | succ m ih =>
      let _ := ih
      change Nontrivial (Matrix (Fin 2) (Fin 2) (ClTower A m))
      infer_instance

/-- Non-commutativity witness for `ClTower A (n + 1)` over any nontrivial ring `A`. -/
theorem clTower_noncomm_witness [Nontrivial A] (n : ℕ) :
    ∃ X Y : ClTower A (n + 1), X * Y ≠ Y * X := by
  let E01 : ClTower A (n + 1) := mat2 0 1 0 0
  let E10 : ClTower A (n + 1) := mat2 0 0 1 0
  refine ⟨E01, E10, ?_⟩
  intro h
  have h00 := congr_arg (fun M : ClTower A (n + 1) => M 0 0) h
  simp only [E01, E10, mul2_00, mat2_00, mat2_01, mat2_10,
    mul_zero, add_zero, zero_add, one_mul] at h00
  have h00' : (1 : ClTower A n) = 0 := h00
  have := clTower_nontrivial (A := A) n
  exact one_ne_zero h00'

end Helpers

/-!
## Archetype $\mathcal{E}_1$: Supertrace Cancellation & Bott Corner Trace Invariance
-/

section ArchetypeE1_UVBulkSubtraction

variable {A : Type u} [Ring A]

/-- Non-unital Bott corner embedding `ι_Bott(X) = diag(X, 0)` from `ClTower A n` into `ClTower A (n + 1)`. -/
def bottEmbed {n : ℕ} (X : ClTower A n) : ClTower A (n + 1) :=
  mat2 X 0 0 0

/-- Unital bulk diagonal embedding `ι_diag(Y) = diag(Y, Y)` from `ClTower A n` into `ClTower A (n + 1)`. -/
def diagEmbed {n : ℕ} (Y : ClTower A n) : ClTower A (n + 1) :=
  mat2 Y 0 0 Y

/-- **Diagonal Supertrace Cancellation & Bott Corner Trace Invariance ($\mathcal{E}_1$)**:
At every scale `n : ℕ`:
1. `towerTrace (diagEmbed Y_bulk) = 2 • towerTrace Y_bulk`,
2. `towerTrace (bottEmbed X_loc) = towerTrace X_loc`,
3. `superTrace (bottEmbed X_loc + diagEmbed Y_bulk) = superTrace X_loc`. -/
theorem bott_trace_and_supertrace_cancellation
    {n : ℕ} (X_loc Y_bulk : ClTower A n) :
    towerTrace (diagEmbed Y_bulk) = 2 • towerTrace Y_bulk ∧
    towerTrace (bottEmbed X_loc) = towerTrace X_loc ∧
    superTrace (bottEmbed X_loc + diagEmbed Y_bulk) = superTrace X_loc := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [towerTrace, diagEmbed]; rw [two_smul]
  · dsimp [towerTrace, bottEmbed]; rw [towerTrace_zero n, add_zero]
  · dsimp [superTrace, bottEmbed, diagEmbed, chiralityOp, towerTrace]
    simp only [Matrix.add_apply, mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      mul_zero, add_zero, zero_add, neg_mul]
    rw [mul_add, towerTrace_add, towerTrace_neg]
    abel

end ArchetypeE1_UVBulkSubtraction

/-!
## Archetype $\mathcal{E}_2$: Direct Limit of Observables $\leftrightarrow$ Inverse Limit of States (Frobenius Reciprocity)
-/

section ArchetypeE2_ObservableStateAdjunction

variable {A : Type u} [Ring A]

/-- Infrared corner state marginalization `P_IR(ρ) = ρ 0 0`. -/
def irStatePullback {n : ℕ} (ρ : ClTower A (n + 1)) : ClTower A n :=
  ρ 0 0

/-- Renormalization-Group (RG) block state marginalization `R_RG(ρ) = ρ 0 0 + ρ 1 1`. -/
def rgStatePullback {n : ℕ} (ρ : ClTower A (n + 1)) : ClTower A n :=
  ρ 0 0 + ρ 1 1

/-- Chiral state polarization `R_chiral(ρ) = ρ 0 0 - ρ 1 1`. -/
def chiralStatePullback {n : ℕ} (ρ : ClTower A (n + 1)) : ClTower A n :=
  ρ 0 0 - ρ 1 1

/-- **Finite-Stage Observable/State Pairing Identities ($\mathcal{E}_2$)**:
For any `(n+1)`-scale state `ρ : ClTower A (n + 1)` and `n`-scale observables `O, B : ClTower A n`:
1. `towerTrace (ρ * bottEmbed O) = towerTrace (irStatePullback ρ * O)`,
2. `superTrace (ρ * bottEmbed O) = superTrace (irStatePullback ρ * O)`,
3. `towerTrace (ρ * diagEmbed B) = towerTrace (rgStatePullback ρ * B)`,
4. `superTrace (ρ * diagEmbed B) = superTrace (chiralStatePullback ρ * B)`. -/
theorem finite_stage_observable_state_pairing
    {n : ℕ} (ρ : ClTower A (n + 1)) (O B : ClTower A n) :
    towerTrace (n := n + 1) (ρ * bottEmbed O) = towerTrace (irStatePullback ρ * O) ∧
    superTrace (n := n + 1) (ρ * bottEmbed O) = superTrace (irStatePullback ρ * O) ∧
    towerTrace (n := n + 1) (ρ * diagEmbed B) = towerTrace (rgStatePullback ρ * B) ∧
    superTrace (n := n + 1) (ρ * diagEmbed B) = superTrace (chiralStatePullback ρ * B) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [towerTrace, bottEmbed, irStatePullback]
    simp [towerTrace_zero n]
  · dsimp [superTrace, towerTrace, chiralityOp, bottEmbed, irStatePullback]
    simp [towerTrace_zero n]
  · dsimp [towerTrace, diagEmbed, rgStatePullback]
    simp only [mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      mul_zero, add_zero, zero_add]
    rw [add_mul, towerTrace_add]
  · dsimp [superTrace, towerTrace, chiralityOp, diagEmbed, chiralStatePullback]
    simp only [mul2_00, mul2_11, mat2_00, mat2_01, mat2_10, mat2_11,
      mul_zero, zero_mul, add_zero, zero_add, neg_mul]
    have h_sub : chiralityOp n * ((ρ 0 0 - ρ 1 1) * B) =
        chiralityOp n * (ρ 0 0 * B) - chiralityOp n * (ρ 1 1 * B) := by noncomm_ring
    rw [h_sub, towerTrace_sub, towerTrace_neg, ← sub_eq_add_neg]

end ArchetypeE2_ObservableStateAdjunction

/-!
## Archetype $\mathcal{E}_3$: Finite-Iteration Transport of Idempotents, Lie Brackets & Hodge Relations
-/

section ArchetypeE3_HomomorphicPropagation

variable {A : Type u} [Ring A]

/-- Multi-step Bott corner embedding `ι_Bott^(k) : ClTower A n → ClTower A (n + k)`. -/
def bottEmbedIter : ∀ {n : ℕ} (k : ℕ), ClTower A n → ClTower A (n + k)
  | _, 0,     X => X
  | _, k + 1, X => bottEmbed (bottEmbedIter k X)

lemma bottEmbed_add {n : ℕ} (X Y : ClTower A n) :
    bottEmbed (X + Y) = bottEmbed X + bottEmbed Y := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma bottEmbed_sub {n : ℕ} (X Y : ClTower A n) :
    bottEmbed (X - Y) = bottEmbed X - bottEmbed Y := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma bottEmbed_mul {n : ℕ} (X Y : ClTower A n) :
    bottEmbed (X * Y) = bottEmbed X * bottEmbed Y := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma bottEmbed_star [StarRing A] {n : ℕ} (X : ClTower A n) :
    bottEmbed (star X) = star (bottEmbed X) := by
  apply ext_fin2 <;> simp [bottEmbed]

lemma bottEmbedIter_add {n : ℕ} (k : ℕ) (X Y : ClTower A n) :
    bottEmbedIter k (X + Y) = bottEmbedIter k X + bottEmbedIter k Y := by
  induction k with
  | zero => rfl
  | succ m ih => dsimp [bottEmbedIter]; rw [ih, bottEmbed_add]

lemma bottEmbedIter_sub {n : ℕ} (k : ℕ) (X Y : ClTower A n) :
    bottEmbedIter k (X - Y) = bottEmbedIter k X - bottEmbedIter k Y := by
  induction k with
  | zero => rfl
  | succ m ih => dsimp [bottEmbedIter]; rw [ih, bottEmbed_sub]

lemma bottEmbedIter_mul {n : ℕ} (k : ℕ) (X Y : ClTower A n) :
    bottEmbedIter k (X * Y) = bottEmbedIter k X * bottEmbedIter k Y := by
  induction k with
  | zero => rfl
  | succ m ih => dsimp [bottEmbedIter]; rw [ih, bottEmbed_mul]

lemma bottEmbedIter_star [StarRing A] {n : ℕ} (k : ℕ) (X : ClTower A n) :
    bottEmbedIter k (star X) = star (bottEmbedIter k X) := by
  induction k with
  | zero => rfl
  | succ m ih => dsimp [bottEmbedIter]; rw [ih, bottEmbed_star]

lemma bottEmbedIter_zero {n : ℕ} (k : ℕ) :
    bottEmbedIter k (0 : ClTower A n) = 0 := by
  induction k with
  | zero => rfl
  | succ m ih => dsimp [bottEmbedIter]; rw [ih]; apply ext_fin2 <;> rfl

/-- **Finite-Iteration Homomorphic Transport of Ring and Hodge Relations ($\mathcal{E}_3$)**:
Across any number of colimit steps `k : ℕ`:
1. For every finite `k : ℕ`, `bottEmbedIter k ⁅X, Y⁆ = ⁅bottEmbedIter k X, bottEmbedIter k Y⁆`,
2. Any self-adjoint idempotent `P * P = P`, `star P = P` propagates to a self-adjoint
   projection `bottEmbedIter k P` with invariant trace `towerTrace (bottEmbedIter k P) = towerTrace P`,
3. The equations `d² = δ² = 0`, `dδd = d`, and `δdδ = δ` transport to
   `ClTower A (n + k)`. These equations alone do not assert that `d` and `δ`
   are star-adjoints. -/
theorem bott_iter_preserves_ring_and_hodge_relations [StarRing A]
    {n : ℕ} (k : ℕ) (X Y : ClTower A n)
    {P : ClTower A n} (hP_idem : P * P = P) (hP_sa : star P = P)
    {d δ : ClTower A n} (hd2 : d * d = 0) (hδ2 : δ * δ = 0)
    (hdδd : d * δ * d = d) (hδdδ : δ * d * δ = δ) :
    let P_k := bottEmbedIter k P
    let d_k := bottEmbedIter k d
    let δ_k := bottEmbedIter k δ
    bottEmbedIter k ⁅X, Y⁆ = ⁅bottEmbedIter k X, bottEmbedIter k Y⁆ ∧
    P_k * P_k = P_k ∧
    star P_k = P_k ∧
    towerTrace P_k = towerTrace P ∧
    d_k * d_k = 0 ∧
    δ_k * δ_k = 0 ∧
    d_k * δ_k * d_k = d_k ∧
    δ_k * d_k * δ_k = δ_k := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Ring.lie_def, bottEmbedIter_sub, bottEmbedIter_mul]
  · rw [← bottEmbedIter_mul, hP_idem]
  · rw [← bottEmbedIter_star, hP_sa]
  · induction k with
    | zero => rfl
    | succ m ih =>
        dsimp [bottEmbedIter]
        rw [(bott_trace_and_supertrace_cancellation (bottEmbedIter m P) 0).2.1, ih]
  · rw [← bottEmbedIter_mul, hd2, bottEmbedIter_zero]
  · rw [← bottEmbedIter_mul, hδ2, bottEmbedIter_zero]
  · rw [← bottEmbedIter_mul, ← bottEmbedIter_mul, hdδd]
  · rw [← bottEmbedIter_mul, ← bottEmbedIter_mul, hδdδ]

end ArchetypeE3_HomomorphicPropagation

/-!
## Archetype $\mathcal{E}_4$: Finite-Iteration Stability of the Spectral Mass-Gap Operator
-/

section ArchetypeE4_MultiStepMassGapCutoffIndependence

variable {A : Type u} [Ring A]

/-- Diagonal scalar lift `a ↦ diag(a, ..., a)` into `ClTower A n`. -/
def towerScalar : ∀ (n : ℕ), A → ClTower A n
  | 0,     a => a
  | n + 1, a => diagEmbed (towerScalar n a)

/-- Spectral mass-gap operator `Δ_n(m₀) = towerScalar n m₀ * (1 - cantorProj n)` in `ClTower A n`. -/
def massGapOp (m₀ : A) (n : ℕ) : ClTower A n :=
  towerScalar n m₀ * (1 - cantorProj n)

lemma towerScalar_bottEmbed (n : ℕ) (m₀ : A) (X : ClTower A n) :
    towerScalar (n + 1) m₀ * bottEmbed X = bottEmbed (towerScalar n m₀ * X) := by
  apply ext_fin2 <;> simp [towerScalar, diagEmbed, bottEmbed]

lemma massGap_one_step_stability (m₀ : A) (n : ℕ) (Ψ : ClTower A n)
    (h_orth : cantorProj n * Ψ = 0) :
    cantorProj (n + 1) * bottEmbed Ψ = 0 ∧
    massGapOp m₀ n * Ψ = towerScalar n m₀ * Ψ ∧
    massGapOp m₀ (n + 1) * bottEmbed Ψ = bottEmbed (massGapOp m₀ n * Ψ) := by
  have h_coer : ∀ {m : ℕ} (Φ : ClTower A m),
      cantorProj m * Φ = 0 → massGapOp m₀ m * Φ = towerScalar m m₀ * Φ := by
    intro m Φ hΦ
    dsimp [massGapOp]
    calc towerScalar m m₀ * (1 - cantorProj m) * Φ
      _ = towerScalar m m₀ * Φ - towerScalar m m₀ * (cantorProj m * Φ) := by noncomm_ring
      _ = towerScalar m m₀ * Φ := by rw [hΦ, mul_zero, sub_zero]
  have h_orth_next : cantorProj (n + 1) * bottEmbed Ψ = 0 := by
    dsimp [cantorProj, bottEmbed]
    apply ext_fin2 <;> simp [h_orth]
  refine ⟨h_orth_next, h_coer Ψ h_orth, ?_⟩
  rw [h_coer (bottEmbed Ψ) h_orth_next, h_coer Ψ h_orth, towerScalar_bottEmbed]

/-- **Finite-Iteration Mass-Gap Stability ($\mathcal{E}_4$)**:
For any `n`-scale excited state `Ψ : ClTower A n` orthogonal to the Cantor vacuum
(`cantorProj n * Ψ = 0`) and any `m₀ : A`, the action of `massGapOp m₀ (n + k)`
on `bottEmbedIter k Ψ` satisfies the finite-stage compatibility identity:
`massGapOp m₀ (n + k) * bottEmbedIter k Ψ = bottEmbedIter k (massGapOp m₀ n * Ψ) = bottEmbedIter k (towerScalar n m₀ * Ψ)`. -/
theorem mass_gap_bott_iter_stability
    (m₀ : A) (n k : ℕ) (Ψ : ClTower A n) (h_orth : cantorProj n * Ψ = 0) :
    cantorProj (n + k) * bottEmbedIter k Ψ = 0 ∧
    massGapOp m₀ (n + k) * bottEmbedIter k Ψ =
      bottEmbedIter k (massGapOp m₀ n * Ψ) ∧
    massGapOp m₀ (n + k) * bottEmbedIter k Ψ =
      bottEmbedIter k (towerScalar n m₀ * Ψ) := by
  have h_base := (massGap_one_step_stability m₀ n Ψ h_orth).2.1
  have h_ind : cantorProj (n + k) * bottEmbedIter k Ψ = 0 ∧
      massGapOp m₀ (n + k) * bottEmbedIter k Ψ =
        bottEmbedIter k (massGapOp m₀ n * Ψ) := by
    induction k with
    | zero => exact ⟨h_orth, rfl⟩
    | succ m ih =>
        rcases ih with ⟨ih_orth, ih_gap⟩
        rcases massGap_one_step_stability m₀ (n + m) (bottEmbedIter m Ψ) ih_orth with
          ⟨h_orth_succ, _, h_stab_succ⟩
        refine ⟨h_orth_succ, ?_⟩
        dsimp [bottEmbedIter]
        change massGapOp m₀ (n + m + 1) * bottEmbed (bottEmbedIter m Ψ) = _
        rw [h_stab_succ, ih_gap]
  refine ⟨h_ind.1, h_ind.2, ?_⟩
  rw [h_ind.2, h_base]

end ArchetypeE4_MultiStepMassGapCutoffIndependence

end InfoGeometry.Algebra.NoncommutativeColimitExtensionMechanisms

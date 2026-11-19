/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.KrausBoundaryDuality
import InfoGeometry.Quantum.FinitePartialTrace
import InfoGeometry.Canonical.CuntzMatrixTraceTower

/-!
# Recorded histories of ordered quantum instruments

A time-dependent binary-outcome instrument acts on an arbitrary finite system
matrix algebra. The internal Kraus labels are summed by the existing `krausMap`;
chronological propagation uses the existing `forwardWord`, with later operators
on the left. The recorded pointer density is the explicitly dephased diagonal
matrix of branch traces on the full dyadic matrix algebra.

Completeness supplies actual prefix marginals, ordinary partial-trace
compatibility, and compatibility of the full-matrix positive functionals under
the existing `A ↦ A ⊗ I₂` tower. Ordinary trace is used throughout this owner.
No commutativity of the system operators, product-state hypothesis, or assumed
compatible state family is used.
-/

noncomputable section

namespace InfoGeometry.Quantum.InstrumentHistory

open Matrix
open InfoGeometry.Quantum.Choi
open InfoGeometry.Quantum.FiniteAttentionCanonicalBridges
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixTraceTower
open scoped ComplexOrder Kronecker

variable {S κ : Type*} [Fintype S] [DecidableEq S] [Fintype κ] [DecidableEq κ]

/-- The chronological word selected by a binary recorded history. -/
def historyWord (K : ℕ → Fin 2 → κ → Matrix S S ℂ) :
    (n : ℕ) → Fin (2 ^ n) → List (κ → Matrix S S ℂ)
  | 0, _ => []
  | n + 1, h =>
      historyWord K n ((stageIndexEquiv n).symm h).1 ++
        [K n ((stageIndexEquiv n).symm h).2]

/-- The unnormalized system matrix after the selected ordered history. -/
def branchState (ρ : Matrix S S ℂ) (K : ℕ → Fin 2 → κ → Matrix S S ℂ)
    (n : ℕ) (h : Fin (2 ^ n)) : Matrix S S ℂ :=
  forwardWord (historyWord K n h) ρ

@[simp] theorem branchState_zero (ρ : Matrix S S ℂ)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ) (h : Fin (2 ^ 0)) :
    branchState ρ K 0 h = ρ := rfl

/-- Appending an outcome applies the later instrument after the previous word. -/
theorem branchState_succ (ρ : Matrix S S ℂ)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ)
    (n : ℕ) (h : Fin (2 ^ n)) (a : Fin 2) :
    branchState ρ K (n + 1) (stageIndexEquiv n (h, a)) =
      krausMap (K n a) (branchState ρ K n h) := by
  simp [branchState, historyWord, forwardWord_append, forwardWord_cons,
    forwardWord_nil]

/-- Every branch remains positive without a completeness assumption. -/
theorem branchState_posSemidef (ρ : Matrix S S ℂ) (hρ : ρ.PosSemidef)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ) (n : ℕ) (h : Fin (2 ^ n)) :
    (branchState ρ K n h).PosSemidef :=
  forwardWord_posSemidef (historyWord K n h) hρ

/-- The history weight is the physical branch trace itself. -/
def historyWeight (ρ : Matrix S S ℂ) (K : ℕ → Fin 2 → κ → Matrix S S ℂ)
    (n : ℕ) (h : Fin (2 ^ n)) : ℂ :=
  trace (branchState ρ K n h)

@[simp] theorem historyWeight_zero (ρ : Matrix S S ℂ)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ) (h : Fin (2 ^ 0)) :
    historyWeight ρ K 0 h = trace ρ := rfl

/-- Complex-order positivity includes both real-valuedness and nonnegativity. -/
theorem historyWeight_nonneg (ρ : Matrix S S ℂ) (hρ : ρ.PosSemidef)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ) (n : ℕ) (h : Fin (2 ^ n)) :
    0 ≤ historyWeight ρ K n h :=
  (branchState_posSemidef ρ hρ K n h).trace_nonneg

/-- The complex trace of a positive branch has no imaginary component. -/
theorem historyWeight_im_eq_zero (ρ : Matrix S S ℂ) (hρ : ρ.PosSemidef)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ) (n : ℕ) (h : Fin (2 ^ n)) :
    (historyWeight ρ K n h).im = 0 :=
  (Complex.nonneg_iff.mp (historyWeight_nonneg ρ hρ K n h)).2.symm

/-- Summing over every recorded and internal outcome preserves ordinary trace. -/
theorem sum_trace_krausMap_outcomes (V : Fin 2 → κ → Matrix S S ℂ)
    (hV : (∑ a : Fin 2, ∑ i : κ, star (V a i) * V a i) = 1)
    (X : Matrix S S ℂ) :
    (∑ a : Fin 2, trace (krausMap (V a) X)) = trace X := by
  have hcomplete :
      (∑ ai : Fin 2 × κ, star (V ai.1 ai.2) * V ai.1 ai.2) = 1 := by
    simpa only [Fintype.sum_prod_type] using hV
  have h := trace_krausMap_of_completeness
    (fun ai : Fin 2 × κ => V ai.1 ai.2) hcomplete X
  simpa only [krausMap, LinearMap.coe_mk, AddHom.coe_mk,
    Fintype.sum_prod_type, trace_sum] using h

/-- The two extensions of a prefix have exactly its original weight. -/
theorem historyWeight_marginal (ρ : Matrix S S ℂ)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ)
    (hK : ∀ n, (∑ a : Fin 2, ∑ i : κ, star (K n a i) * K n a i) = 1)
    (n : ℕ) (h : Fin (2 ^ n)) :
    (∑ a : Fin 2, historyWeight ρ K (n + 1) (stageIndexEquiv n (h, a))) =
      historyWeight ρ K n h := by
  simp only [historyWeight, branchState_succ]
  exact sum_trace_krausMap_outcomes (K n) (hK n) (branchState ρ K n h)

/-- The weights sum to the trace of the actual input matrix at every length. -/
theorem sum_historyWeight (ρ : Matrix S S ℂ)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ)
    (hK : ∀ n, (∑ a : Fin 2, ∑ i : κ, star (K n a i) * K n a i) = 1)
    (n : ℕ) :
    (∑ h : Fin (2 ^ n), historyWeight ρ K n h) = trace ρ := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (∑ h : Fin (2 ^ (n + 1)), historyWeight ρ K (n + 1) h) =
            ∑ ha : Fin (2 ^ n) × Fin 2,
              historyWeight ρ K (n + 1) (stageIndexEquiv n ha) :=
          (Equiv.sum_comp (stageIndexEquiv n) (historyWeight ρ K (n + 1))).symm
        _ = ∑ h : Fin (2 ^ n),
              ∑ a : Fin 2, historyWeight ρ K (n + 1) (stageIndexEquiv n (h, a)) :=
          Fintype.sum_prod_type _
        _ = ∑ h : Fin (2 ^ n), historyWeight ρ K n h := by
          apply Finset.sum_congr rfl
          intro h _
          exact historyWeight_marginal ρ K hK n h
        _ = trace ρ := ih

/-- The specified dephased pointer density on the entire finite matrix algebra. -/
def historyDensity (ρ : Matrix S S ℂ) (K : ℕ → Fin 2 → κ → Matrix S S ℂ)
    (n : ℕ) : MatrixStage n :=
  diagonal (historyWeight ρ K n)

theorem historyDensity_posSemidef (ρ : Matrix S S ℂ) (hρ : ρ.PosSemidef)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ) (n : ℕ) :
    (historyDensity ρ K n).PosSemidef :=
  Matrix.PosSemidef.diagonal (historyWeight_nonneg ρ hρ K n)

theorem historyDensity_trace (ρ : Matrix S S ℂ)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ)
    (hK : ∀ n, (∑ a : Fin 2, ∑ i : κ, star (K n a i) * K n a i) = 1)
    (n : ℕ) :
    trace (historyDensity ρ K n) = trace ρ := by
  rw [historyDensity, trace_diagonal]
  exact sum_historyWeight ρ K hK n

/-- Ordinary partial trace of the next actual density recovers this density. -/
theorem historyDensity_partialTrace (ρ : Matrix S S ℂ)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ)
    (hK : ∀ n, (∑ a : Fin 2, ∑ i : κ, star (K n a i) * K n a i) = 1)
    (n : ℕ) :
    partialTraceSecondOp
        ((Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)).symm
          (historyDensity ρ K (n + 1))) = historyDensity ρ K n := by
  have hreindex :
      (Matrix.reindexAlgEquiv ℂ ℂ (stageIndexEquiv n)).symm
          (historyDensity ρ K (n + 1)) =
        diagonal (fun ha : Fin (2 ^ n) × Fin 2 =>
          historyWeight ρ K (n + 1) (stageIndexEquiv n ha)) := by
    exact Matrix.submatrix_diagonal_equiv _ (stageIndexEquiv n)
  rw [hreindex, partialTraceSecondOp_diagonal
    (fun h a => historyWeight ρ K (n + 1) (stageIndexEquiv n (h, a)))]
  congr 1
  funext h
  exact historyWeight_marginal ρ K hK n h

/-- A full pointer observable is evaluated by ordinary trace against the density. -/
def historyFunctional (ρ : Matrix S S ℂ)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ) (n : ℕ) : MatrixStage n →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap (Fin (2 ^ n)) ℂ ℂ).comp
    (LinearMap.mulRight ℂ (historyDensity ρ K n))

theorem historyFunctional_apply (ρ : Matrix S S ℂ)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ) (n : ℕ) (X : MatrixStage n) :
    historyFunctional ρ K n X = trace (X * historyDensity ρ K n) := rfl

theorem historyFunctional_eq_sum (ρ : Matrix S S ℂ)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ) (n : ℕ) (X : MatrixStage n) :
    historyFunctional ρ K n X = ∑ h : Fin (2 ^ n), X h h * historyWeight ρ K n h := by
  simp only [historyFunctional_apply, historyDensity, trace, diag_apply, mul_diagonal]

/-- Positivity holds on every positive full matrix, not just elementary tensors. -/
theorem historyFunctional_nonneg (ρ : Matrix S S ℂ) (hρ : ρ.PosSemidef)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ) (n : ℕ)
    (X : MatrixStage n) (hX : X.PosSemidef) :
    0 ≤ historyFunctional ρ K n X := by
  rw [historyFunctional_eq_sum]
  exact Finset.sum_nonneg fun h _ =>
    mul_nonneg hX.diag_nonneg (historyWeight_nonneg ρ hρ K n h)

theorem historyFunctional_one (ρ : Matrix S S ℂ)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ)
    (hK : ∀ n, (∑ a : Fin 2, ∑ i : κ, star (K n a i) * K n a i) = 1)
    (n : ℕ) :
    historyFunctional ρ K n 1 = trace ρ := by
  rw [historyFunctional_apply, one_mul, historyDensity_trace ρ K hK]

/-- Compatibility under the actual full-matrix successor embedding. -/
theorem historyFunctional_step (ρ : Matrix S S ℂ)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ)
    (hK : ∀ n, (∑ a : Fin 2, ∑ i : κ, star (K n a i) * K n a i) = 1)
    (n : ℕ) (X : MatrixStage n) :
    historyFunctional ρ K (n + 1) (concreteStep n X) = historyFunctional ρ K n X := by
  rw [historyFunctional_eq_sum, historyFunctional_eq_sum]
  rw [← Equiv.sum_comp (stageIndexEquiv n)
    (fun h => concreteStep n X h h * historyWeight ρ K (n + 1) h)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  have hentry (a : Fin 2) :
      concreteStep n X (stageIndexEquiv n (h, a)) (stageIndexEquiv n (h, a)) = X h h := by
    simp [concreteStep, Matrix.reindexAlgEquiv]
  simp_rw [hentry]
  rw [← Finset.mul_sum, historyWeight_marginal ρ K hK]

/-- Every filtered transition preserves the constructed functional. -/
theorem historyFunctional_transition (ρ : Matrix S S ℂ)
    (K : ℕ → Fin 2 → κ → Matrix S S ℂ)
    (hK : ∀ n, (∑ a : Fin 2, ∑ i : κ, star (K n a i) * K n a i) = 1)
    {i j : ℕ} (hij : i ≤ j) (X : MatrixStage i) :
    historyFunctional ρ K j (concreteMap hij X) = historyFunctional ρ K i X := by
  induction hij with
  | refl => rw [concreteMap_id]; rfl
  | @step j hij ih =>
      change historyFunctional ρ K (j + 1) (map concreteData (Nat.le.step hij) X) = _
      rw [map_succ]
      exact (historyFunctional_step ρ K hK j (concreteMap hij X)).trans ih

end InfoGeometry.Quantum.InstrumentHistory

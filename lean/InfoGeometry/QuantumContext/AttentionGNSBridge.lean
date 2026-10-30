/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.AttentionKMSState
import InfoGeometry.Prequantum.GNSAction

/-!
# Attention states in the repository's algebraic GNS action

Uses the owned `RealAlgebraicState`, `AbstractGNSState`, and
`RepresentationState`; no second quotient or action is introduced. The
generic diagonal input is nonnegative and normalized. The final declaration
specializes it to the existing softmax attention weights.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.AttentionGNSBridge

open InfoGeometry.Prequantum.AlgebraicGNSState
open InfoGeometry.Prequantum.GNSBridge
open InfoGeometry.Prequantum.GNSAction
open InfoGeometry.QuantumContext.AttentionKMSState
open Matrix

variable {ι : Type*} [Fintype ι]

/-- Weighted diagonal evaluation as a real linear functional on matrices. -/
def weightedMatrixFunctional (w : ι → ℝ) : Matrix ι ι ℝ →ₗ[ℝ] ℝ where
  toFun A := ∑ i, w i * A i i
  map_add' A B := by
    simp [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    change (∑ i, w i * (c * A i i)) = c * (∑ i, w i * A i i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      w i * (c * A i i) = (w i * c) * A i i := by rw [mul_assoc]
      _ = (c * w i) * A i i := by rw [mul_comm (w i) c]
      _ = c * (w i * A i i) := by rw [mul_assoc]

variable [DecidableEq ι]

/-- Positive normalized algebraic state associated to diagonal weights. -/
def weightedMatrixState (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) : RealAlgebraicState (Matrix ι ι ℝ) where
  toLinearMap := weightedMatrixFunctional w
  normalized := by
    simp [weightedMatrixFunctional, hsum]
  positive := by
    intro A
    change 0 ≤ ∑ i, w i * (star A * A) i i
    have hstar : star A = A.transpose := by
      ext i j
      simp [Matrix.star_apply, Matrix.transpose_apply]
    rw [hstar]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg (hw i)
    apply Finset.sum_nonneg
    intro j hj
    exact mul_self_nonneg (A j i)
  symmetric := by
    intro A B
    change (∑ i, w i * (star B * A) i i) =
      ∑ i, w i * (star A * B) i i
    have hstarA : star A = A.transpose := by
      ext i j
      simp [Matrix.star_apply, Matrix.transpose_apply]
    have hstarB : star B = B.transpose := by
      ext i j
      simp [Matrix.star_apply, Matrix.transpose_apply]
    simp only [hstarA, hstarB, Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_comm (A j i) (B j i)]

/-- The algebraic state's quadratic form agrees with the existing diagonal
matrix GNS quadratic form. -/
theorem weightedMatrixState_quadratic_eq_gnsInner (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (A : Matrix ι ι ℝ) :
    (weightedMatrixState w hw hsum).eval (star A * A) =
      InfoGeometry.QuantumContext.MatrixGNS.gnsInner (Matrix.diagonal w) A A := by
  change (∑ i, w i * (star A * A) i i) = _
  have hstar : star A = A.transpose := by
    ext i j
    simp [Matrix.star_apply, Matrix.transpose_apply]
  rw [hstar]
  rw [InfoGeometry.QuantumContext.MatrixGNS.gnsInner_self_diagonal]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Wrap the diagonal state in the existing quotient representation, using
the repository's theorem that its null set is a left ideal. -/
def weightedRepresentationState (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    RepresentationState (Matrix ι ι ℝ) where
  state := ⟨weightedMatrixState w hw hsum⟩
  null_left_ideal := by
    intro a x hx
    change (weightedMatrixState w hw hsum).eval (star x * x) = 0 at hx
    change (weightedMatrixState w hw hsum).eval (star (a * x) * (a * x)) = 0
    have hx' : InfoGeometry.QuantumContext.MatrixGNS.gnsLeftIdeal
        (Matrix.diagonal w) x := by
      change InfoGeometry.QuantumContext.MatrixGNS.gnsInner
        (Matrix.diagonal w) x x = 0
      rw [← weightedMatrixState_quadratic_eq_gnsInner w hw hsum x]
      exact hx
    have hax := InfoGeometry.QuantumContext.MatrixGNS.gnsLeftIdeal_mul_left
      w hw x a hx'
    change InfoGeometry.QuantumContext.MatrixGNS.gnsInner
      (Matrix.diagonal w) (a * x) (a * x) = 0 at hax
    rw [weightedMatrixState_quadratic_eq_gnsInner w hw hsum (a * x)]
    exact hax

/-- The existing attention state equals weighted diagonal evaluation at its
softmax weights. -/
theorem attentionState_eq_weightedMatrixFunctional
    (logits : ι → ℝ) (β : ℝ) (A : Matrix ι ι ℝ) :
    attentionState logits β A =
      weightedMatrixFunctional (softmaxWeight logits β) A := by
  rw [attentionState_eq_sum]
  rfl

/-- The attention state wrapped in the existing algebraic GNS quotient action. -/
def attentionRepresentationState [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) : RepresentationState (Matrix ι ι ℝ) :=
  weightedRepresentationState (softmaxWeight logits β)
    (fun i => le_of_lt (softmaxWeight_pos logits β i))
    (softmaxWeight_sum_one logits β)

/-- The pruned diagonal state in the repository's existing quotient action. -/
def prunedRepresentationState
    (pw : PrunedWeights ι) : RepresentationState (Matrix ι ι ℝ) :=
  weightedRepresentationState pw.weights pw.nonneg pw.sum_one

/-- The quotient carrier for a pruned attention state, using the existing
`AbstractGNSState.gnsQuotient`. -/
abbrev prunedGNSQuotient (pw : PrunedWeights ι) :=
  AbstractGNSState.gnsQuotient (prunedRepresentationState pw).state

/-- The pruned-state action is the repository's established GNS quotient
action. -/
def prunedAction (pw : PrunedWeights ι) (A : Matrix ι ι ℝ) :
    prunedGNSQuotient pw → prunedGNSQuotient pw :=
  (prunedRepresentationState pw).act A

/-- The pruned-state vacuum is the quotient class of the unit. -/
def prunedVacuum (pw : PrunedWeights ι) : prunedGNSQuotient pw :=
  (prunedRepresentationState pw).vacuum

/-- Eviction makes the quotient vacuum non-separating: the existing nonzero
projection witness lies in the state null set and hence annihilates the
vacuum in the actual GNS quotient action. -/
theorem pruned_action_vacuum_not_separating (pw : PrunedWeights ι) :
    ∃ E : Matrix ι ι ℝ, E ≠ 0 ∧
      prunedAction pw E (prunedVacuum pw) =
        Quotient.mk (AbstractGNSState.gnsSetoid (prunedRepresentationState pw).state) 0 := by
  obtain ⟨E, hE0, hE_null⟩ := pruned_cache_has_nontrivial_null_ideal pw
  have hstar : star E = E.transpose := by
    ext i j
    simp [Matrix.star_apply, Matrix.transpose_apply]
  have hgns : InfoGeometry.QuantumContext.MatrixGNS.gnsInner
      (Matrix.diagonal pw.weights) E E = 0 := by
    rw [← prunedState_quadratic_eq_gnsInner]
    exact hE_null
  have hstate : (weightedMatrixState pw.weights pw.nonneg pw.sum_one).eval
      (star E * E) = 0 := by
    rw [weightedMatrixState_quadratic_eq_gnsInner]
    simpa [hstar] using hgns
  have hnull : E ∈ (prunedRepresentationState pw).state.gnsNullSet := hstate
  refine ⟨E, hE0, ?_⟩
  exact (RepresentationState.act_vacuum_eq_zero_iff_null (prunedRepresentationState pw) E).2 hnull

/-- The existing GNS vacuum is cyclic for every `RepresentationState`: each
quotient class is represented by the action of some algebra element. -/
theorem representationState_vacuum_cyclic
    (S : RepresentationState (Matrix ι ι ℝ))
    (q : AbstractGNSState.gnsQuotient S.state) :
    ∃ A : Matrix ι ι ℝ, S.act A S.vacuum = q := by
  refine Quotient.inductionOn q ?_
  intro A
  exact ⟨A, S.act_vacuum A⟩

/-- Evaluation of the wrapped representation state is the existing attention
state functional. -/
theorem attentionRepresentationState_eval [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) (A : Matrix ι ι ℝ) :
    (attentionRepresentationState logits β).state.eval A =
      attentionState logits β A := by
  rw [attentionState_eq_weightedMatrixFunctional]
  rfl

/-- The state functional on the actual algebraic GNS representation satisfies
the finite attention KMS boundary identity. This transports the existing
matrix-state theorem through the repository's GNS state wrapper; it does not
assert an analytic KMS condition for a completed operator algebra. -/
theorem attentionRepresentationState_kms [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) (A B : Matrix ι ι ℝ) :
    (attentionRepresentationState logits β).state.eval
        (A * (attentionDensityMatrix logits β * B * attentionDensityMatrixInv logits β)) =
      (attentionRepresentationState logits β).state.eval (B * A) := by
  calc
    (attentionRepresentationState logits β).state.eval
        (A * (attentionDensityMatrix logits β * B * attentionDensityMatrixInv logits β))
      = attentionState logits β
          (A * (attentionDensityMatrix logits β * B * attentionDensityMatrixInv logits β)) :=
            attentionRepresentationState_eval logits β _
    _ = attentionState logits β (B * A) := attentionState_kms logits β A B
    _ = (attentionRepresentationState logits β).state.eval (B * A) :=
          (attentionRepresentationState_eval logits β _).symm

/-- Softmax's GNS quotient vacuum is cyclic, with the quotient action supplied
by the existing representation-state owner. -/
theorem attention_vacuum_cyclic [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ)
    (q : AbstractGNSState.gnsQuotient
      (attentionRepresentationState logits β).state) :
    ∃ A : Matrix ι ι ℝ,
      (attentionRepresentationState logits β).act A
        (attentionRepresentationState logits β).vacuum = q :=
  representationState_vacuum_cyclic (attentionRepresentationState logits β) q

/-- With strictly positive softmax weights, the quotient vacuum is separating
for the existing left action. This is a quotient-level statement: an operator
annihilating the vacuum has zero class, and faithfulness forces that operator
to vanish. -/
theorem attention_action_vacuum_separating [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) (A : Matrix ι ι ℝ) :
    (attentionRepresentationState logits β).act A
        (attentionRepresentationState logits β).vacuum =
      Quotient.mk
        (AbstractGNSState.gnsSetoid (attentionRepresentationState logits β).state) 0 ↔ A = 0 := by
  rw [RepresentationState.act_vacuum_eq_zero_iff_null]
  constructor
  · intro hnull
    have hquad : (attentionRepresentationState logits β).state.state.eval
        (star A * A) = 0 := hnull
    have hstar : star A = A.transpose := by
      ext i j
      simp [Matrix.star_apply, Matrix.transpose_apply]
    have hAttention : attentionState logits β (A.transpose * A) = 0 := by
      rw [← attentionRepresentationState_eval]
      simpa [AbstractGNSState.eval, hstar] using hquad
    exact (attentionState_faithful logits β A).mp hAttention
  · intro hA
    have hstar : star A = A.transpose := by
      ext i j
      simp [Matrix.star_apply, Matrix.transpose_apply]
    have hfaith := (attentionState_faithful logits β A).mpr hA
    have hquad : (attentionRepresentationState logits β).state.state.eval
        (star A * A) = 0 := by
      change (attentionRepresentationState logits β).state.eval
        (star A * A) = 0
      rw [attentionRepresentationState_eval]
      simpa [AbstractGNSState.eval, hstar] using hfaith
    change (attentionRepresentationState logits β).state.state.eval
      (star A * A) = 0
    exact hquad

end InfoGeometry.QuantumContext.AttentionGNSBridge

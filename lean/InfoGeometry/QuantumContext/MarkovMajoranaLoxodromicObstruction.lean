/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Tactic.NoncommRing
import InfoGeometry.QuantumContext.MarkovJordanWignerMetriplecticBridge
import InfoGeometry.QuantumContext.MarkovGroupInversePetzSupport
import InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel
import InfoGeometry.Canonical.Cl11LeftRightDoubleBridge

/-!
# Gate-2 obstruction: a Markov range axis need not commute with a Majorana axis

This candidate uses the actual first Clifford matrix stage `MatStage 1` (whose
index is `Idx 1 = Idx 0 × Fin 2`), the repository's row-softmax constructor,
and `majoranaDifference 0` from the Jordan--Wigner owner. The score matrix has
diagonal `log 3` and off-diagonal `0`, so its transition is the symmetric,
strictly positive two-state kernel with diagonal `3/4` and off-diagonal `1/4`.
The displayed group inverse is checked against the owner definition; it is not
an assumed inverse. The resulting involution `2E - 1`, where `E = (1-P)G`,
anticommutes with the genuine Majorana matrix. Thus the two proposed axes do
not automatically form commuting loxodromic axes on this carrier.

This is only a concrete same-carrier algebraic obstruction. It does not
identify token indices with occupation-basis labels, nor does it identify a
Transformer trajectory with a Lorentzian or hyperbolic loxodrome.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.MarkovMajoranaLoxodromicObstruction

open Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.TowerMatrix
open InfoGeometry.Clifford.JordanWignerBridge
open InfoGeometry.Canonical.Cl11LeftRightDoubleBridge
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovDrazin.JordanWigner
open InfoGeometry.QuantumContext.FiniteSoftmaxMarkovKernel
open InfoGeometry.Canonical.HartwigSouriauFrameDrazin

abbrev StageOne := MatStage 1

@[simp] theorem stageOneIndexEquiv_symm_apply (i : Fin 2) :
    stageOneIndexEquiv.symm i = ((0 : Fin 1), i) := rfl

/-- The recursive first-stage matrix index is canonically the two-element
index; this equivalence makes its finite sums computationally transparent. -/
@[simp] theorem sum_idxOne (f : Idx 1 → ℝ) :
    (∑ i, f i) = f ((0 : Fin 1), (0 : Fin 2)) +
      f ((0 : Fin 1), (1 : Fin 2)) := by
  rw [← Equiv.sum_comp stageOneIndexEquiv.symm f]
  simp only [Fin.sum_univ_two, stageOneIndexEquiv_symm_apply]
  rfl

/-- Symmetric score logits: `log 3` on the diagonal and zero off diagonal. -/
def twoModeScores (i j : Idx 1) : ℝ :=
  if i.2 = j.2 then Real.log 3 else 0

/-- The transition matrix produced by the repository's softmax owner. -/
def twoModeTransition : Matrix (Idx 1) (Idx 1) ℝ :=
  softmaxAttentionMatrix twoModeScores

/-- Explicit group inverse for the Laplacian of `twoModeTransition`. -/
def twoModeGroupInverse : Matrix (Idx 1) (Idx 1) ℝ :=
  fun i j => if i.2 = j.2 then 1 else -1

/-- Entrywise readout of the source-defined softmax matrix. -/
theorem twoModeTransition_apply (i j : Idx 1) :
    twoModeTransition i j = if i.2 = j.2 then (3 : ℝ) / 4 else 1 / 4 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [twoModeTransition, twoModeScores, softmaxAttentionMatrix,
      softmaxAttentionKernel, queryPartitionFunction, gibbsCouplingWeight,
      InfoGeometry.Clifford.TowerMatrix.Idx, Fintype.sum_prod_type,
      Fin.sum_univ_one, Fin.sum_univ_two, stageOneIndexEquiv,
      Real.exp_log]

/-- The concrete matrix is a genuine group inverse of its softmax Laplacian. -/
theorem twoModeGroupInverse_spec :
    IsGroupInverse (1 - twoModeTransition) twoModeGroupInverse := by
  unfold IsGroupInverse
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [twoModeTransition_apply, twoModeGroupInverse,
        Matrix.mul_apply, InfoGeometry.Clifford.TowerMatrix.Idx,
        Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two,
        Matrix.one_apply]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [twoModeTransition_apply, twoModeGroupInverse,
        Matrix.mul_apply, InfoGeometry.Clifford.TowerMatrix.Idx,
        Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two,
        Matrix.one_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [twoModeTransition_apply, twoModeGroupInverse,
        Matrix.mul_apply, InfoGeometry.Clifford.TowerMatrix.Idx,
        Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two,
        Matrix.one_apply]

/-- The actual Markov range involution on the first Clifford stage. -/
def markovRangeInvolution : StageOne :=
  (2 : ℝ) • markovRangeIdempotent twoModeTransition twoModeGroupInverse -
    (1 : StageOne)

/-- The source-defined Majorana matrix at the site introduced at stage one. -/
def firstMajorana : StageOne := majoranaDifference 0

/-- The range involution and actual Majorana direction anticommute. -/
theorem rangeInvolution_majorana_anticommute :
    markovRangeInvolution * firstMajorana =
      -(firstMajorana * markovRangeInvolution) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [markovRangeInvolution, firstMajorana, markovRangeIdempotent,
      twoModeTransition_apply, twoModeGroupInverse, majoranaDifference,
      jw_u_new, jw_v_new, globalChirality, kronPow,
      InfoGeometry.Clifford.JordanWignerBridge.a_dagger_base,
      InfoGeometry.Clifford.JordanWignerBridge.a_base,
      Matrix.mul_apply, Matrix.kronecker_apply,
      InfoGeometry.Clifford.TowerMatrix.Idx, Fintype.sum_prod_type,
      Fin.sum_univ_one, Fin.sum_univ_two, Matrix.one_apply]

/-- The range involution squares to one, hence is nonzero. -/
theorem rangeInvolution_sq : markovRangeInvolution * markovRangeInvolution = 1 := by
  have hG := twoModeGroupInverse_spec
  have hE := markovRangeIdempotent_idempotent
    twoModeTransition twoModeGroupInverse hG
  change markovRangeIdempotent twoModeTransition twoModeGroupInverse *
      markovRangeIdempotent twoModeTransition twoModeGroupInverse =
    markovRangeIdempotent twoModeTransition twoModeGroupInverse at hE
  dsimp [markovRangeInvolution]
  noncomm_ring [hE]

/-- The Majorana direction is nonzero by the source owner theorem. -/
theorem firstMajorana_ne_zero : firstMajorana ≠ 0 := by
  exact majoranaDifference_ne_zero 0

/-- The anti-commutation is a genuine noncommutation witness. -/
theorem rangeInvolution_majorana_noncommute :
    markovRangeInvolution * firstMajorana ≠
      firstMajorana * markovRangeInvolution := by
  intro hcomm
  have hanti := rangeInvolution_majorana_anticommute
  have hsum : markovRangeInvolution * firstMajorana +
      markovRangeInvolution * firstMajorana = 0 := by
    have hprod_neg : markovRangeInvolution * firstMajorana =
        -(markovRangeInvolution * firstMajorana) := by
      calc
        markovRangeInvolution * firstMajorana =
            -(firstMajorana * markovRangeInvolution) := hanti
        _ = -(markovRangeInvolution * firstMajorana) :=
          congrArg Neg.neg hcomm.symm
    calc
      markovRangeInvolution * firstMajorana +
          markovRangeInvolution * firstMajorana =
        markovRangeInvolution * firstMajorana +
          -(markovRangeInvolution * firstMajorana) := by
            exact congrArg
              (fun z : StageOne => markovRangeInvolution * firstMajorana + z)
              hprod_neg
      _ = 0 := add_neg_cancel _
  have hprod : markovRangeInvolution * firstMajorana = 0 := by
    have hscalar : (2 : ℝ) •
        (markovRangeInvolution * firstMajorana) = 0 := by
      simpa [two_smul] using hsum
    exact (smul_eq_zero.mp hscalar).resolve_left (by norm_num)
  have hprodJ := congrArg (fun X : StageOne => X * firstMajorana) hprod
  have hprodJ' : markovRangeInvolution *
      (firstMajorana * firstMajorana) = 0 := by
    calc
      markovRangeInvolution * (firstMajorana * firstMajorana) =
          (markovRangeInvolution * firstMajorana) * firstMajorana := by
        rw [mul_assoc]
      _ = 0 := by simpa using hprodJ
  change markovRangeInvolution *
      (majoranaDifference 0 * majoranaDifference 0) = 0 at hprodJ'
  rw [majoranaDifference_sq] at hprodJ'
  have hHzero : markovRangeInvolution = 0 := by
    have hneg : -markovRangeInvolution = 0 := by
      simpa using hprodJ'
    exact neg_eq_zero.mp hneg
  have hunit := congrArg (fun X : StageOne => X * markovRangeInvolution) hHzero
  rw [rangeInvolution_sq] at hunit
  simpa using hunit

end InfoGeometry.QuantumContext.MarkovMajoranaLoxodromicObstruction

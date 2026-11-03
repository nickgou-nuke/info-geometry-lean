/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TensorQuotientCurvatureWeights
import InfoGeometry.Cartan.Involution

/-! # Canonical weight projections of the tangent quotient

The existing Cartan involution projectors split every quotient direction
into opposite weights. The exact quotient curvature contains only the two
mixed-weight terms.
-/

noncomputable section

namespace InfoGeometry.Canonical.TensorQuotientWeightDecomposition

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.TensorCurvatureTangentQuotient
open InfoGeometry.Canonical.TensorQuotientCutInvolution
open InfoGeometry.Canonical.TensorQuotientCurvatureWeights

set_option maxHeartbeats 1000000
noncomputable local instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

/-- The linear endomorphism underlying the cut involution. -/
def cutWeightOperator (P : Limit) (hP : P * P = P) :
    Module.End ℝ (LimitDeriv ⧸ (cutEvaluation P).ker) :=
  (cutQuotientInvolution P hP).toLinearMap

/-- The cut endomorphism is an involution in the full endomorphism ring. -/
theorem cutWeightOperator_involution (P : Limit) (hP : P * P = P) :
    InfoGeometry.Cartan.IsCartanInvolution (cutWeightOperator P hP) := by
  apply LinearMap.ext
  intro u
  change cutQuotientInvolution P hP (cutQuotientInvolution P hP u) = u
  exact cutInner_quotient_involutive P hP u

/-- The canonical `+1` and `-1` projection operators. -/
def cutWeightPlus (P : Limit) (hP : P * P = P) :=
  InfoGeometry.Cartan.Pplus (cutWeightOperator P hP)

def cutWeightMinus (P : Limit) (hP : P * P = P) :=
  InfoGeometry.Cartan.Pminus (cutWeightOperator P hP)

/-- The two operators are complementary, mutually annihilating idempotents
on the actual quotient vector space. -/
theorem cutWeight_projectors (P : Limit) (hP : P * P = P) :
    cutWeightPlus P hP * cutWeightPlus P hP = cutWeightPlus P hP ∧
    cutWeightMinus P hP * cutWeightMinus P hP = cutWeightMinus P hP ∧
    cutWeightPlus P hP * cutWeightMinus P hP = 0 ∧
    cutWeightMinus P hP * cutWeightPlus P hP = 0 ∧
    cutWeightPlus P hP + cutWeightMinus P hP = 1 := by
  exact ⟨InfoGeometry.Cartan.Pplus_idempotent _ (cutWeightOperator_involution P hP),
    InfoGeometry.Cartan.Pminus_idempotent _ (cutWeightOperator_involution P hP),
    InfoGeometry.Cartan.Pplus_comp_Pminus _ (cutWeightOperator_involution P hP),
    InfoGeometry.Cartan.Pminus_comp_Pplus _ (cutWeightOperator_involution P hP),
    InfoGeometry.Cartan.Pplus_add_Pminus_eq_id _⟩

/-- Every quotient direction has a canonical sum of opposite-weight parts. -/
theorem cutWeight_decompose (P : Limit) (hP : P * P = P)
    (u : LimitDeriv ⧸ (cutEvaluation P).ker) :
    u = cutWeightPlus P hP u + cutWeightMinus P hP u :=
  InfoGeometry.Cartan.decompose (cutWeightOperator P hP) (cutWeightOperator_involution P hP) u

/-- The positive component has weight `+1`. -/
theorem cutWeightPlus_eigen (P : Limit) (hP : P * P = P)
    (u : LimitDeriv ⧸ (cutEvaluation P).ker) :
    cutQuotientInvolution P hP (cutWeightPlus P hP u) = cutWeightPlus P hP u := by
  have h := congrArg (fun f : Module.End ℝ (LimitDeriv ⧸ (cutEvaluation P).ker) => f u)
    (InfoGeometry.Cartan.involution_comp_Pplus (cutWeightOperator P hP)
      (cutWeightOperator_involution P hP))
  exact h

/-- The negative component has weight `-1`. -/
theorem cutWeightMinus_eigen (P : Limit) (hP : P * P = P)
    (u : LimitDeriv ⧸ (cutEvaluation P).ker) :
    cutQuotientInvolution P hP (cutWeightMinus P hP u) = -cutWeightMinus P hP u := by
  have h := congrArg (fun f : Module.End ℝ (LimitDeriv ⧸ (cutEvaluation P).ker) => f u)
    (InfoGeometry.Cartan.involution_comp_Pminus (cutWeightOperator P hP)
      (cutWeightOperator_involution P hP))
  exact h

/-- The quotient curvature is the sum of its two mixed-weight components. -/
theorem quotientCurvature_mixed_weight_decomposition (P : Limit) (hP : P * P = P)
    (u v : LimitDeriv ⧸ (cutEvaluation P).ker) :
    quotientCurvature P u v =
      quotientCurvature P (cutWeightPlus P hP u) (cutWeightMinus P hP v) +
      quotientCurvature P (cutWeightMinus P hP u) (cutWeightPlus P hP v) := by
  calc
    quotientCurvature P u v =
        quotientCurvature P (cutWeightPlus P hP u + cutWeightMinus P hP u)
          (cutWeightPlus P hP v + cutWeightMinus P hP v) :=
      congrArg₂ (quotientCurvature P) (cutWeight_decompose P hP u) (cutWeight_decompose P hP v)
    _ = _ := by
      rw [quotientCurvature_add_left, quotientCurvature_add_right, quotientCurvature_add_right,
        quotientCurvature_positive_weights_zero P hP _ _ (cutWeightPlus_eigen P hP u)
          (cutWeightPlus_eigen P hP v),
        quotientCurvature_negative_weights_zero P hP _ _ (cutWeightMinus_eigen P hP u)
          (cutWeightMinus_eigen P hP v)]
      simp

end InfoGeometry.Canonical.TensorQuotientWeightDecomposition

end

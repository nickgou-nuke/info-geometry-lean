/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.CanonicalZornAnalytic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

namespace InfoGeometry.Canonical

noncomputable section

open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

abbrev EndCZ := CZ →L[ℝ] CZ

def automorphismConstraintAt (X Y : CZ) : EndCZ → CZ :=
  fun A => A (zMul X Y) - zMul (A X) (A Y)

noncomputable def automorphismConstraintDerivativeAt
    (X Y : CZ) (A : EndCZ) : EndCZ →L[ℝ] CZ :=
  ContinuousLinearMap.apply ℝ CZ (zMul X Y) -
    (isBoundedBilinearMap_zMul.deriv (A X, A Y)).comp
      ((ContinuousLinearMap.apply ℝ CZ X).prod
        (ContinuousLinearMap.apply ℝ CZ Y))

theorem hasStrictFDerivAt_automorphismConstraintAt
    (X Y : CZ) (A : EndCZ) :
    HasStrictFDerivAt (automorphismConstraintAt X Y)
      (automorphismConstraintDerivativeAt X Y A) A := by
  have h₁ : HasStrictFDerivAt (fun B : EndCZ => B (zMul X Y))
      (ContinuousLinearMap.apply ℝ CZ (zMul X Y)) A := by
    exact (ContinuousLinearMap.apply ℝ CZ (zMul X Y)).hasStrictFDerivAt
      |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun B => rfl)
  have h₂ : HasStrictFDerivAt (fun B : EndCZ => (B X, B Y))
      ((ContinuousLinearMap.apply ℝ CZ X).prod
        (ContinuousLinearMap.apply ℝ CZ Y)) A := by
    exact ((ContinuousLinearMap.apply ℝ CZ X).prod
      (ContinuousLinearMap.apply ℝ CZ Y)).hasStrictFDerivAt
      |>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun B => rfl)
  have h₃ := isBoundedBilinearMap_zMul.hasStrictFDerivAt (A X, A Y)
  have h₄ := HasStrictFDerivAt.comp A h₃ h₂
  convert h₁.sub h₄ <;> rfl

theorem automorphismConstraintDerivativeAt_apply
    (X Y : CZ) (D : EndCZ) :
    automorphismConstraintDerivativeAt X Y
        (ContinuousLinearMap.id ℝ CZ) D =
      D (zMul X Y) - zMul (D X) Y - zMul X (D Y) := by
  unfold automorphismConstraintDerivativeAt
  simp only [sub_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply]
  rw [isBoundedBilinearMap_zMul.deriv_apply]
  abel

theorem automorphismConstraintDerivativeAt_eq_zero_iff
    (X Y : CZ) (D : EndCZ) :
    automorphismConstraintDerivativeAt X Y
        (ContinuousLinearMap.id ℝ CZ) D = 0 ↔
      D (zMul X Y) = zMul (D X) Y + zMul X (D Y) := by
  rw [automorphismConstraintDerivativeAt_apply]
  constructor
  · intro h
    apply sub_eq_zero.mp
    calc
      D (zMul X Y) - (zMul (D X) Y + zMul X (D Y)) =
          D (zMul X Y) - zMul (D X) Y - zMul X (D Y) := by abel
      _ = 0 := h
  · intro h
    calc
      D (zMul X Y) - zMul (D X) Y - zMul X (D Y) =
          D (zMul X Y) - (zMul (D X) Y + zMul X (D Y)) := by abel
      _ = (zMul (D X) Y + zMul X (D Y)) - (zMul (D X) Y + zMul X (D Y)) := by rw [h]
      _ = 0 := sub_self _

end
end InfoGeometry.Canonical

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.CanonicalZornAnalytic

/-! The differential of one multiplicativity equation on the ambient
continuous endomorphism space. -/

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
    simpa only using
      (ContinuousLinearMap.apply ℝ CZ (zMul X Y)).hasStrictFDerivAt
  have h₂ : HasStrictFDerivAt (fun B : EndCZ => (B X, B Y))
      ((ContinuousLinearMap.apply ℝ CZ X).prod
        (ContinuousLinearMap.apply ℝ CZ Y)) A := by
    simpa only using
      ((ContinuousLinearMap.apply ℝ CZ X).prod
        (ContinuousLinearMap.apply ℝ CZ Y)).hasStrictFDerivAt
  have h₃ := isBoundedBilinearMap_zMul.hasStrictFDerivAt (A X, A Y)
  have h₄ := h₃.comp A h₂
  simpa [automorphismConstraintAt, automorphismConstraintDerivativeAt] using h₁.sub h₄

theorem automorphismConstraintDerivativeAt_apply
    (X Y : CZ) (D : EndCZ) :
    automorphismConstraintDerivativeAt X Y
        (ContinuousLinearMap.id ℝ CZ) D =
      D (zMul X Y) - zMul (D X) Y - zMul X (D Y) := by
  ext <;>
    simp [automorphismConstraintDerivativeAt,
      IsBoundedBilinearMap.deriv_apply] <;> ring

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
      _ = 0 := sub_eq_zero.mpr h

end
end InfoGeometry.Canonical

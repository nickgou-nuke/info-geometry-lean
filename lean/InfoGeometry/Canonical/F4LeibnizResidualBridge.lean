import InfoGeometry.Algebra.BaezF4H3Zorn

/-! The F4 constraint is a residual, not a second product. -/

namespace InfoGeometry.Canonical.F4LeibnizResidualBridge

noncomputable section

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn

abbrev H3 := H3Zorn ℝ
abbrev EndH3 := Module.End ℝ H3

def residual (D : EndH3) (X Y : H3) : H3 :=
  D (X * Y) - D X * Y - X * D Y

theorem residual_zero_iff (D : EndH3) :
    (∀ X Y, residual D X Y = 0) ↔ H3ZornJordanDerivation D := by
  constructor
  · intro h X Y
    have hxy := h X Y
    dsimp [residual] at hxy
    apply sub_eq_zero.mp
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hxy
  · intro h X Y
    dsimp [residual]
    rw [h]
    simp [sub_eq_add_neg, add_assoc]

theorem inner_derivation_residual_zero (a b : H3) :
    ∀ X Y, residual (jordanInnerDerivation (R := ℝ) a b) X Y = 0 := by
  intro X Y
  exact (residual_zero_iff _).mpr
    (jordanInnerDerivation_isLeibniz (R := ℝ) a b) X Y

end
end InfoGeometry.Canonical.F4LeibnizResidualBridge

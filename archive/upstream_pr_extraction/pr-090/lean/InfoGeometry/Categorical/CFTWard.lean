import Mathlib.Data.Real.Basic

theorem ward_identity_2pt {Δ1 Δ2 z1 z2 C : ℝ} (h1 : C * (z1 - z2) * (Δ1 - Δ2) = 0) (h2 : z1 - z2 ≠ 0) (h3 : C ≠ 0) : Δ1 = Δ2 := by
  cases mul_eq_zero.mp h1 with
  | inl h4 =>
    cases mul_eq_zero.mp h4 with
    | inl h5 => exact False.elim (h3 h5)
    | inr h6 => exact False.elim (h2 h6)
  | inr h7 =>
    exact sub_eq_zero.mp h7

import InfoGeometry.Topology.MobiusGeometry

open Complex
open InfoGeometry

theorem fixed_point_quadratic_test (M : MobiusTransform) (hc : M.c ≠ 0) (γ : ℂ) :
    M.is_fixed_point (some γ) ↔ M.c * γ^2 - (M.a - M.d) * γ - M.b = 0 := by
  dsimp [MobiusTransform.is_fixed_point, MobiusTransform.eval]
  by_cases h_den : M.c * γ + M.d = 0
  · rw [if_pos h_den]
    constructor
    · intro h; cases h
    · intro h
      have hd : M.d = -M.c * γ := by
        have h1 : M.d + M.c * γ = 0 := by
          calc M.d + M.c * γ = M.c * γ + M.d := by ring
            _ = 0 := h_den
        exact eq_neg_of_add_eq_zero_left h1
      have hb : M.b = -M.a * γ := by
        have h1 : M.b = (M.c * γ^2 - (M.a - M.d) * γ) - (M.c * γ^2 - (M.a - M.d) * γ - M.b) := by ring
        rw [h, sub_zero] at h1
        have h_alg : M.c * γ^2 - (M.a - M.d) * γ = M.c * γ^2 - M.a * γ + M.d * γ := by ring
        rw [h_alg, hd] at h1
        have h_fin : M.c * γ^2 - M.a * γ + (-M.c * γ) * γ = -M.a * γ := by ring
        rw [h_fin] at h1
        exact h1
      have hdet := M.det_ne_zero
      have h_zero : M.a * M.d - M.b * M.c = 0 := by
        calc M.a * M.d - M.b * M.c = M.a * (-M.c * γ) - (-M.a * γ) * M.c := by rw [hd, hb]
          _ = 0 := by ring
      exact (hdet h_zero).elim
  · rw [if_neg h_den]
    constructor
    · intro h
      have h1 := Option.some.inj h
      have h2 : γ * (M.c * γ + M.d) = M.a * γ + M.b := (div_eq_iff_mul_eq h_den).mp h1
      have h3 : M.c * γ^2 - (M.a - M.d) * γ - M.b = γ * (M.c * γ + M.d) - (M.a * γ + M.b) := by ring
      rw [h3, h2, sub_self]
    · intro h
      congr 1
      apply (div_eq_iff_mul_eq h_den).mpr
      have h3 : M.a * γ + M.b = γ * (M.c * γ + M.d) - (M.c * γ^2 - (M.a - M.d) * γ - M.b) := by ring
      rw [h3, h, sub_zero]

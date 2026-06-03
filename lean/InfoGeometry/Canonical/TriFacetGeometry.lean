/-
#### BUCKET 1: CLOSED FINITE THEOREMS
[Fully verified lemmas with zero remaining dependencies or open goals. Fully checked by the kernel.]
- `P_sum` — the three operators partition unity
- `T_pow4` — T⁴ = T² under T³ = T
- `P_hyp_idem` — hyperbolic projector is idempotent
- `P_ell_idem` — elliptic projector is idempotent
- `P_par_idem` — parabolic projector is idempotent
- `P_hyp_ell_orth` — hyperbolic and elliptic are orthogonal
- `P_hyp_par_orth` — hyperbolic and parabolic are orthogonal
- `P_ell_par_orth` — elliptic and parabolic are orthogonal

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
[None in this module.]

#### BUCKET 3: OPEN CLOSURE DEBT
[None in this module.]
-/

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

namespace InfoGeometry.Canonical.TriFacetGeometry

variable {F : Type*} [CommRing F] [Invertible (2 : F)]

/-- The Hyperbolic projection operator P_hyp = (T² + T)/2. -/
def P_hyp (T : F) : F := ⅟(2 : F) * (T^2 + T)

/-- The Elliptic projection operator P_ell = (T² - T)/2. -/
def P_ell (T : F) : F := ⅟(2 : F) * (T^2 - T)

/-- The Parabolic (Harmonic Kernel) projection operator P_par = 1 - T². -/
def P_par (T : F) : F := 1 - T^2

/-- The three projection operators partition unity. -/
theorem P_sum (T : F) : P_hyp T + P_ell T + P_par T = 1 := by
  unfold P_hyp P_ell P_par
  field_simp
  ring

/-- T³ = T implies T⁴ = T². -/
theorem T_pow4 (T : F) (hT : T^3 = T) : T^4 = T^2 := by
  calc
    T^4 = T * T^3 := by ring
    _ = T * T := by rw [hT]
    _ = T^2 := by ring

/-- The Hyperbolic projector is idempotent under T³ = T. -/
theorem P_hyp_idem (T : F) (hT : T^3 = T) : P_hyp T * P_hyp T = P_hyp T := by
  unfold P_hyp
  have hT4 : T^4 = T^2 := T_pow4 T hT
  have h_sq : (T^2 + T)^2 = 2 * (T^2 + T) := by
    calc
      (T^2 + T)^2 = T^4 + 2 * T^3 + T^2 := by ring
      _ = T^2 + 2 * T + T^2 := by rw [hT4, hT]
      _ = 2 * (T^2 + T) := by ring
  calc
    (⅟(2 : F) * (T^2 + T)) * (⅟(2 : F) * (T^2 + T)) = (⅟(2 : F))^2 * (T^2 + T)^2 := by ring
    _ = (⅟(2 : F))^2 * (2 * (T^2 + T)) := by rw [h_sq]
    _ = (⅟(2 : F) * ⅟(2 : F) * 2) * (T^2 + T) := by ring
    _ = (⅟(2 : F) * (⅟(2 : F) * (2 : F))) * (T^2 + T) := by ring
    _ = (⅟(2 : F) * 1) * (T^2 + T) := by rw [invOf_mul_self (2 : F)]
    _ = ⅟(2 : F) * (T^2 + T) := by ring

/-- The Elliptic projector is idempotent under T³ = T. -/
theorem P_ell_idem (T : F) (hT : T^3 = T) : P_ell T * P_ell T = P_ell T := by
  unfold P_ell
  have hT4 : T^4 = T^2 := T_pow4 T hT
  have h_sq : (T^2 - T)^2 = 2 * (T^2 - T) := by
    calc
      (T^2 - T)^2 = T^4 - 2 * T^3 + T^2 := by ring
      _ = T^2 - 2 * T + T^2 := by rw [hT4, hT]
      _ = 2 * (T^2 - T) := by ring
  calc
    (⅟(2 : F) * (T^2 - T)) * (⅟(2 : F) * (T^2 - T)) = (⅟(2 : F))^2 * (T^2 - T)^2 := by ring
    _ = (⅟(2 : F))^2 * (2 * (T^2 - T)) := by rw [h_sq]
    _ = (⅟(2 : F) * ⅟(2 : F) * 2) * (T^2 - T) := by ring
    _ = (⅟(2 : F) * (⅟(2 : F) * (2 : F))) * (T^2 - T) := by ring
    _ = (⅟(2 : F) * 1) * (T^2 - T) := by rw [invOf_mul_self (2 : F)]
    _ = ⅟(2 : F) * (T^2 - T) := by ring

/-- The Parabolic projector is idempotent under T³ = T. -/
theorem P_par_idem (T : F) (hT : T^3 = T) : P_par T * P_par T = P_par T := by
  unfold P_par
  have hT4 : T^4 = T^2 := T_pow4 T hT
  calc
    (1 - T^2) * (1 - T^2) = 1 - 2 * T^2 + T^4 := by ring
    _ = 1 - 2 * T^2 + T^2 := by rw [hT4]
    _ = 1 - T^2 := by ring

/-- Hyperbolic and Elliptic projectors are orthogonal under T³ = T. -/
theorem P_hyp_ell_orth (T : F) (hT : T^3 = T) : P_hyp T * P_ell T = 0 := by
  unfold P_hyp P_ell
  have hT4 : T^4 = T^2 := T_pow4 T hT
  calc
    (⅟(2 : F) * (T^2 + T)) * (⅟(2 : F) * (T^2 - T)) = (⅟(2 : F))^2 * (T^4 - T^2) := by ring
    _ = (⅟(2 : F))^2 * (T^2 - T^2) := by rw [hT4]
    _ = 0 := by ring

/-- Hyperbolic and Parabolic projectors are orthogonal under T³ = T. -/
theorem P_hyp_par_orth (T : F) (hT : T^3 = T) : P_hyp T * P_par T = 0 := by
  unfold P_hyp P_par
  have hT4 : T^4 = T^2 := T_pow4 T hT
  calc
    (⅟(2 : F) * (T^2 + T)) * (1 - T^2) = ⅟(2 : F) * (T^2 + T - T^4 - T^3) := by ring
    _ = ⅟(2 : F) * (T^2 + T - T^2 - T) := by rw [hT4, hT]
    _ = 0 := by ring

/-- Elliptic and Parabolic projectors are orthogonal under T³ = T. -/
theorem P_ell_par_orth (T : F) (hT : T^3 = T) : P_ell T * P_par T = 0 := by
  unfold P_ell P_par
  have hT4 : T^4 = T^2 := T_pow4 T hT
  calc
    (⅟(2 : F) * (T^2 - T)) * (1 - T^2) = ⅟(2 : F) * (T^2 - T - T^4 + T^3) := by ring
    _ = ⅟(2 : F) * (T^2 - T - T^2 + T) := by rw [hT4, hT]
    _ = 0 := by ring

end InfoGeometry.Canonical.TriFacetGeometry

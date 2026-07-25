import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.FenchelExpLogScalar

Scalar exp/log Fenchel-Bregman core identities (no Taylor usage).

Primal potential: `f(x) = exp x`.
Dual potential: `f*(y) = y * log y - y` for `y > 0`.
-/

namespace InfoGeometry.Canonical.FenchelExpLogScalar

noncomputable section

/-- Primal potential. -/
def f (x : ℝ) : ℝ := Real.exp x

/-- Dual potential on positive domain. -/
def fStar (y : ℝ) : ℝ := y * Real.log y - y

/-- Primal gradient map. -/
def gradPrimal (x : ℝ) : ℝ := Real.exp x

/-- Dual gradient map. -/
def gradDual (y : ℝ) : ℝ := Real.log y

/-- Gradient inverse relation: `gradDual (gradPrimal x) = x`. -/
theorem gradDual_gradPrimal (x : ℝ) :
    gradDual (gradPrimal x) = x := by
  unfold gradDual gradPrimal
  simpa using Real.log_exp x

/-- Gradient inverse relation on positive domain: `gradPrimal (gradDual y) = y`. -/
theorem gradPrimal_gradDual (y : ℝ) (hy : 0 < y) :
    gradPrimal (gradDual y) = y := by
  unfold gradPrimal gradDual
  simpa using Real.exp_log hy

/-- Exponential is the additive-to-multiplicative morphism. -/
theorem gradPrimal_add_morphism (x y : ℝ) :
    gradPrimal (x + y) = gradPrimal x * gradPrimal y := by
  unfold gradPrimal
  simpa using Real.exp_add x y

/-- Logarithm is the multiplicative-to-additive morphism on positive domain. -/
theorem gradDual_mul_morphism (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    gradDual (x * y) = gradDual x + gradDual y := by
  unfold gradDual
  simpa using Real.log_mul (ne_of_gt hx) (ne_of_gt hy)

/-- Logarithm sends identity to additive identity. -/
theorem gradDual_one :
    gradDual 1 = 0 := by
  unfold gradDual
  simpa using Real.log_one

/-- Exponential sends additive identity to multiplicative identity. -/
theorem gradPrimal_zero :
    gradPrimal 0 = 1 := by
  unfold gradPrimal
  simpa using Real.exp_zero

/-- Fenchel equality for the exp/log pair at matched coordinates `y = exp x`. -/
theorem fenchel_identity_matched (x : ℝ) :
    f x + fStar (gradPrimal x) = x * gradPrimal x := by
  unfold f fStar gradPrimal
  rw [Real.log_exp]
  ring

/-- Fenchel--Young inequality for `f(x)=exp x`, `f*(y)=y log y - y` on `y>0`. -/
theorem fenchel_young_exp (x y : ℝ) (hy : 0 < y) :
    x * y ≤ f x + fStar y := by
  unfold f fStar
  have htpos : 0 < Real.exp x / y := by
    exact div_pos (Real.exp_pos x) hy
  have hlog : Real.log (Real.exp x / y) ≤ Real.exp x / y - 1 := by
    simpa using Real.log_le_sub_one_of_pos htpos
  have hy_mul : y * Real.log (Real.exp x / y) ≤ Real.exp x - y := by
    have hy0 : 0 ≤ y := le_of_lt hy
    have hmul := mul_le_mul_of_nonneg_left hlog hy0
    have hdiv : y * (Real.exp x / y - 1) = Real.exp x - y := by
      field_simp [ne_of_gt hy]
    simpa [hdiv] using hmul
  have hlogsplit : Real.log (Real.exp x / y) = x - Real.log y := by
    rw [Real.log_div (ne_of_gt (Real.exp_pos x)) (ne_of_gt hy), Real.log_exp]
  have hxy : x * y = y * Real.log (Real.exp x / y) + y * Real.log y := by
    rw [hlogsplit]
    ring
  calc
    x * y = y * Real.log (Real.exp x / y) + y * Real.log y := hxy
    _ ≤ (Real.exp x - y) + y * Real.log y := by
          have hadd := add_le_add_right hy_mul (y * Real.log y)
          simpa [add_assoc, add_comm, add_left_comm] using hadd
    _ = Real.exp x + (y * Real.log y - y) := by ring

/-- Fenchel--Young equality at matched coordinates `y = exp x`. -/
theorem fenchel_young_exp_eq (x : ℝ) :
    x * gradPrimal x = f x + fStar (gradPrimal x) := by
  symm
  exact fenchel_identity_matched x

/--
Primal Bregman divergence for `f(x)=exp x` against reference `x₀`.
-/
def bregmanPrimal (x x0 : ℝ) : ℝ :=
  f x - f x0 - gradPrimal x0 * (x - x0)

/-- Closed form of primal Bregman divergence for exp potential. -/
theorem bregmanPrimal_closed (x x0 : ℝ) :
    bregmanPrimal x x0 =
      Real.exp x - Real.exp x0 - Real.exp x0 * (x - x0) := by
  rfl

/-- Nonnegativity of primal Bregman divergence for the exponential potential. -/
theorem bregmanPrimal_nonneg (x x0 : ℝ) :
    0 ≤ bregmanPrimal x x0 := by
  unfold bregmanPrimal f gradPrimal
  have hx : Real.exp x = Real.exp x0 * Real.exp (x - x0) := by
    calc
      Real.exp x = Real.exp ((x - x0) + x0) := by ring_nf
      _ = Real.exp (x - x0) * Real.exp x0 := by rw [Real.exp_add]
      _ = Real.exp x0 * Real.exp (x - x0) := by ring
  rw [hx]
  have hcore : 0 ≤ Real.exp (x - x0) - 1 - (x - x0) := by
    have haux : 1 + (x - x0) ≤ Real.exp (x - x0) := by
      simpa [add_comm] using Real.add_one_le_exp (x - x0)
    linarith
  have hpos : 0 < Real.exp x0 := Real.exp_pos x0
  have hmul : 0 ≤ Real.exp x0 * (Real.exp (x - x0) - 1 - (x - x0)) :=
    mul_nonneg (le_of_lt hpos) hcore
  simpa [left_distrib, right_distrib, mul_assoc, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using hmul

/-- Zero characterization for the exponential Bregman divergence. -/
theorem bregmanPrimal_eq_zero_iff (x x0 : ℝ) :
    bregmanPrimal x x0 = 0 ↔ x = x0 := by
  constructor
  · intro h
    unfold bregmanPrimal f gradPrimal at h
    have hx : Real.exp x = Real.exp x0 * Real.exp (x - x0) := by
      calc
        Real.exp x = Real.exp ((x - x0) + x0) := by ring_nf
        _ = Real.exp (x - x0) * Real.exp x0 := by rw [Real.exp_add]
        _ = Real.exp x0 * Real.exp (x - x0) := by ring
    rw [hx] at h
    have hfactor :
        Real.exp x0 * (Real.exp (x - x0) - 1 - (x - x0)) = 0 := by
      linarith
    have hcore : Real.exp (x - x0) - 1 - (x - x0) = 0 := by
      have hpos : Real.exp x0 ≠ 0 := by exact ne_of_gt (Real.exp_pos x0)
      exact (mul_eq_zero.mp hfactor).resolve_left hpos
    have hsub : x - x0 = 0 := by
      by_contra hne
      have hlt : x - x0 + 1 < Real.exp (x - x0) := Real.add_one_lt_exp hne
      have hgt : 0 < Real.exp (x - x0) - 1 - (x - x0) := by linarith
      linarith
    linarith
  · intro h
    subst h
    unfold bregmanPrimal f gradPrimal
    ring

/--
Dual Bregman divergence for `f*(y)=y log y - y` against reference `y₀`.
-/
def bregmanDual (y y0 : ℝ) : ℝ :=
  fStar y - fStar y0 - gradDual y0 * (y - y0)

/-- Closed form of dual Bregman divergence. -/
theorem bregmanDual_closed (y y0 : ℝ) :
    bregmanDual y y0 =
      y * Real.log y - y - (y0 * Real.log y0 - y0) - Real.log y0 * (y - y0) := by
  rfl

/-- KL-form of the dual Bregman divergence (for positive `y,y0`). -/
theorem bregmanDual_eq_kl_form (y y0 : ℝ) (hy : 0 < y) (hy0 : 0 < y0) :
    bregmanDual y y0 = y * Real.log (y / y0) - (y - y0) := by
  unfold bregmanDual fStar gradDual
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hy0)]
  ring

/-- Dual Bregman divergence at matched exponential coordinates. -/
theorem bregmanDual_exp_closed (x x0 : ℝ) :
    bregmanDual (Real.exp x) (Real.exp x0) =
      Real.exp x * (x - x0) - (Real.exp x - Real.exp x0) := by
  unfold bregmanDual fStar gradDual
  rw [Real.log_exp, Real.log_exp]
  ring

/--
Primal/dual Bregman equality at matched coordinates:
`D_f(x,x0) = D_{f*}(exp x0, exp x)`.
-/
theorem bregmanPrimal_eq_bregmanDual_matched (x x0 : ℝ) :
    bregmanPrimal x x0 = bregmanDual (Real.exp x0) (Real.exp x) := by
  unfold bregmanPrimal bregmanDual f fStar gradPrimal gradDual
  rw [Real.log_exp, Real.log_exp]
  ring

/-- Matched-coordinate dual divergence in explicit KL form. -/
theorem bregmanDual_exp_eq_kl_form (x x0 : ℝ) :
    bregmanDual (Real.exp x) (Real.exp x0) =
      Real.exp x * Real.log (Real.exp x / Real.exp x0) - (Real.exp x - Real.exp x0) := by
  exact bregmanDual_eq_kl_form (Real.exp x) (Real.exp x0) (Real.exp_pos x) (Real.exp_pos x0)

/-- Fenchel objective for `f(x)=exp x`: `x ↦ y*x - exp x`. -/
def fenchelObj (y x : ℝ) : ℝ := y * x - f x

/-- Every Fenchel objective value is bounded above by `f*(y)` on `y>0`. -/
theorem fenchelObj_le_fStar (x y : ℝ) (hy : 0 < y) :
    fenchelObj y x ≤ fStar y := by
  unfold fenchelObj
  have h := fenchel_young_exp x y hy
  linarith

/-- The witness point `x = log y` attains the Fenchel upper bound on `y>0`. -/
theorem fenchelObj_at_log_eq_fStar (y : ℝ) (hy : 0 < y) :
    fenchelObj y (Real.log y) = fStar y := by
  unfold fenchelObj f fStar
  rw [Real.exp_log hy]

/--
Supremum readout via explicit witness:
`f*(y)` is the greatest element of the range of the Fenchel objective
`x ↦ y*x - exp x` on `y>0`.
-/
theorem fenchelObj_isGreatest (y : ℝ) (hy : 0 < y) :
    IsGreatest (Set.range (fenchelObj y)) (fStar y) := by
  refine ⟨?mem, ?upper⟩
  · refine ⟨Real.log y, ?_⟩
    exact fenchelObj_at_log_eq_fStar y hy
  · intro z hz
    rcases hz with ⟨x, rfl⟩
    exact fenchelObj_le_fStar x y hy

end

end InfoGeometry.Canonical.FenchelExpLogScalar

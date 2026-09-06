import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace InfoGeometry.Arithmetic.ZetaCayleyKlein

open Complex

def F (β : ℂ) : ℂ := 2 - β

def C (β : ℂ) : ℂ := star β

def R (β : ℂ) : ℂ := 2 - star β

@[simp] theorem F_apply (β : ℂ) : F β = 2 - β := rfl
@[simp] theorem C_apply (β : ℂ) : C β = star β := rfl
@[simp] theorem R_apply (β : ℂ) : R β = 2 - star β := rfl

theorem starRingEnd_two :
    (starRingEnd ℂ) (2 : ℂ) = 2 :=
  map_ofNat (starRingEnd ℂ) 2

@[simp]
theorem F_F (β : ℂ) :
    F (F β) = β := by
  dsimp [F]
  ring

@[simp]
theorem C_C (β : ℂ) :
    C (C β) = β := by
  dsimp [C]
  exact star_star β

@[simp]
theorem R_R (β : ℂ) :
    R (R β) = β := by
  dsimp [R]
  have hsub : (starRingEnd ℂ) (2 - (starRingEnd ℂ) β) = (starRingEnd ℂ) (2 : ℂ) - (starRingEnd ℂ) ((starRingEnd ℂ) β) :=
    map_sub (starRingEnd ℂ) 2 ((starRingEnd ℂ) β)
  have hss : (starRingEnd ℂ) ((starRingEnd ℂ) β) = β := star_star β
  rw [hsub, starRingEnd_two, hss]
  ring

theorem F_comp_C (β : ℂ) :
    F (C β) = R β := by
  dsimp [F, C, R]

theorem C_comp_F (β : ℂ) :
    C (F β) = R β := by
  dsimp [F, C, R]
  have hsub : (starRingEnd ℂ) (2 - β) = (starRingEnd ℂ) (2 : ℂ) - (starRingEnd ℂ) β :=
    map_sub (starRingEnd ℂ) 2 β
  rw [hsub, starRingEnd_two]

theorem F_comp_R (β : ℂ) :
    F (R β) = C β := by
  dsimp [F, R, C]
  ring

theorem R_comp_F (β : ℂ) :
    R (F β) = C β := by
  dsimp [F, R, C]
  have hsub : (starRingEnd ℂ) (2 - β) = (starRingEnd ℂ) (2 : ℂ) - (starRingEnd ℂ) β :=
    map_sub (starRingEnd ℂ) 2 β
  rw [hsub, starRingEnd_two]
  ring

/-- 🏆 THEOREM 1: The fixed points of R are precisely the critical line Re(β) = 1. -/
theorem R_fixed_iff (β : ℂ) :
    R β = β ↔ β.re = 1 := by
  dsimp [R]
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp only [sub_re, conj_re] at hre
    have h2re : (2 : ℂ).re = 2 := rfl
    rw [h2re] at hre
    linarith
  · intro h
    apply Complex.ext
    · simp only [sub_re, conj_re]
      have h2re : (2 : ℂ).re = 2 := rfl
      rw [h2re]
      linarith
    · simp only [sub_im, conj_im]
      have h2im : (2 : ℂ).im = 0 := rfl
      rw [h2im, sub_neg_eq_add, zero_add]

/-- The Cayley coordinate z = β / (2 - β). -/
noncomputable def cayleyZ (β : ℂ) : ℂ :=
  β / (2 - β)

/-- Inverse Cayley coordinate β = 2z / (1 + z). -/
noncomputable def invCayleyZ (z : ℂ) : ℂ :=
  (2 * z) / (1 + z)

@[simp]
theorem cayleyZ_zero :
    cayleyZ 0 = 0 := by
  dsimp [cayleyZ]
  simp

@[simp]
theorem cayleyZ_one :
    cayleyZ 1 = 1 := by
  dsimp [cayleyZ]
  have h21 : (2 : ℂ) - 1 = 1 := by ring
  rw [h21, div_one]

theorem invCayleyZ_cayleyZ (β : ℂ) (h : 2 - β ≠ 0) :
    invCayleyZ (cayleyZ β) = β := by
  dsimp [invCayleyZ, cayleyZ]
  have hden : 1 + β / (2 - β) = 2 / (2 - β) := by
    have h1 : (1 : ℂ) = (2 - β) / (2 - β) := (div_self h).symm
    rw [h1, ← add_div]
    ring_nf
  rw [hden]
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hcancel : (2 * β) / (2 - β) / (2 / (2 - β)) = (2 * β) / 2 :=
    div_div_div_cancel_right₀ (a := 2 * β) (b := 2) (c := 2 - β) h
  have hmul : 2 * (β / (2 - β)) = (2 * β) / (2 - β) := by ring
  rw [hmul, hcancel, mul_div_cancel_left₀ β h2]

/-- On the critical line β = 1 + it, the Cayley coordinate is (1 + it) / (1 - it). -/
theorem cayleyZ_critical (t : ℝ) :
    cayleyZ (1 + (t : ℂ) * I) = (1 + (t : ℂ) * I) / (1 - (t : ℂ) * I) := by
  dsimp [cayleyZ]
  have h : (2 : ℂ) - (1 + (t : ℂ) * I) = 1 - (t : ℂ) * I := by ring
  rw [h]

/-- 🏆 THEOREM 2: The critical line Re(β) = 1 maps precisely to the unit circle |z| = 1. -/
theorem normSq_cayleyZ_critical (t : ℝ) :
    normSq (cayleyZ (1 + (t : ℂ) * I)) = 1 := by
  rw [cayleyZ_critical, normSq_div]
  have hnum : normSq (1 + (t : ℂ) * I) = 1 + t^2 := by
    simp [normSq]
    ring
  have hden : normSq (1 - (t : ℂ) * I) = 1 + t^2 := by
    simp [normSq]
    ring
  rw [hnum, hden]
  have hpos : (1 + t^2 : ℝ) ≠ 0 := by positivity
  exact div_self hpos

/-- 🏆 THEOREM 2b: Exact general biconditional on the domain 2 - β ≠ 0:
    |z(β)|² = 1 ↔ Re(β) = 1. -/
theorem normSq_cayleyZ_eq_one_iff (β : ℂ) (hβ : 2 - β ≠ 0) :
    normSq (cayleyZ β) = 1 ↔ β.re = 1 := by
  dsimp [cayleyZ]
  rw [normSq_div]
  have hden_pos : 0 < normSq (2 - β) := normSq_pos.mpr hβ
  have hden_ne : normSq (2 - β) ≠ 0 := ne_of_gt hden_pos
  rw [div_eq_one_iff_eq hden_ne]
  simp only [normSq_apply, sub_re, sub_im]
  have h2re : (2 : ℂ).re = 2 := rfl
  have h2im : (2 : ℂ).im = 0 := rfl
  rw [h2re, h2im]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- 🏆 THEOREM 3: The functional equation F induces inversion z ↦ 1/z. -/
theorem cayleyZ_F (β : ℂ) :
    cayleyZ (F β) = (cayleyZ β)⁻¹ := by
  dsimp [cayleyZ, F]
  have hnum : (2 : ℂ) - (2 - β) = β := by ring
  rw [hnum, inv_div]

/-- 🏆 THEOREM 4: Complex conjugation C induces z ↦ star(z). -/
theorem cayleyZ_C (β : ℂ) :
    cayleyZ (C β) = star (cayleyZ β) := by
  dsimp [cayleyZ, C]
  have hdiv : (starRingEnd ℂ) (β / (2 - β)) = (starRingEnd ℂ) β / (starRingEnd ℂ) (2 - β) :=
    map_div₀ (starRingEnd ℂ) β (2 - β)
  have hsub : (starRingEnd ℂ) (2 - β) = (starRingEnd ℂ) (2 : ℂ) - (starRingEnd ℂ) β :=
    map_sub (starRingEnd ℂ) 2 β
  rw [hdiv, hsub, starRingEnd_two]

/-- 🏆 THEOREM 5: Critical reflection R induces anti-holomorphic reflection z ↦ 1/star(z). -/
theorem cayleyZ_R (β : ℂ) :
    cayleyZ (R β) = (star (cayleyZ β))⁻¹ := by
  rw [← F_comp_C, cayleyZ_F, cayleyZ_C]

/-- 🏆 THEOREM 6: Reflection across the critical circle fixes |z| = 1 pointwise. -/
theorem circle_reflection_fixed (z : ℂ) (hz : normSq z = 1) :
    (star z)⁻¹ = z := by
  have hz_ne : z ≠ 0 := by
    intro h0; subst h0; simp at hz
  have h_star_ne : star z ≠ 0 := by
    intro h0
    have hz0 : z = 0 := by simpa using congrArg star h0
    exact hz_ne hz0
  have hmul : star z * z = (normSq z : ℂ) := by
    rw [mul_comm]
    exact mul_conj z
  have h1 : star z * z = 1 := by
    rw [hmul, hz, ofReal_one]
  exact inv_eq_of_mul_eq_one_right h1

/-- 🏆 THEOREM 6b: Full biconditional for critical circle reflection: (star z)⁻¹ = z ↔ |z|² = 1. -/
theorem circle_reflection_fixed_iff (z : ℂ) (hz : z ≠ 0) :
    (star z)⁻¹ = z ↔ normSq z = 1 := by
  have h_star_ne : star z ≠ 0 := by
    intro h0
    have hz0 : z = 0 := by simpa using congrArg star h0
    exact hz hz0
  constructor
  · intro h
    have h1 : star z * z = star z * (star z)⁻¹ := by
      congr 1
      exact h.symm
    have h2 : star z * (star z)⁻¹ = 1 := mul_inv_cancel₀ h_star_ne
    have h3 : star z * z = (normSq z : ℂ) := by
      rw [mul_comm]
      exact mul_conj z
    rw [h3, h2] at h1
    have hre := congrArg Complex.re h1
    simp only [ofReal_re, one_re] at hre
    exact hre
  · intro h
    exact circle_reflection_fixed z h

/-- The half-period twisted glide involution τ(z) = - 1 / star(z). -/
noncomputable def tauGlide (z : ℂ) : ℂ :=
  - (star z)⁻¹

@[simp]
theorem tauGlide_apply (z : ℂ) :
    tauGlide z = - (star z)⁻¹ := rfl

/-- 🏆 THEOREM 7: The glide involution is an exact involution: τ(τ(z)) = z. -/
theorem tauGlide_involutive (z : ℂ) :
    tauGlide (tauGlide z) = z := by
  dsimp [tauGlide]
  have h_star_neg : starRingEnd ℂ (- (starRingEnd ℂ z)⁻¹) = - (starRingEnd ℂ (starRingEnd ℂ z)⁻¹) := map_neg _ _
  have h_star_inv : starRingEnd ℂ (starRingEnd ℂ z)⁻¹ = (starRingEnd ℂ (starRingEnd ℂ z))⁻¹ := map_inv₀ _ _
  have h_star_star : starRingEnd ℂ (starRingEnd ℂ z) = z := star_star z
  rw [h_star_neg, h_star_inv, h_star_star, neg_inv, neg_neg, inv_inv]

/-- 🏆 THEOREM 8: The glide involution has NO fixed points on ℂˣ (Free Involution).
    Because z = - 1 / star(z) ⟹ |z|² = -1, which is impossible for real normSq. -/
theorem tauGlide_has_no_fixed_points (z : ℂ) (hz : z ≠ 0) :
    tauGlide z ≠ z := by
  intro h_fix
  have h_star_ne : star z ≠ 0 := by
    intro h0
    have hz0 : z = 0 := by simpa using congrArg star h0
    exact hz hz0
  dsimp [tauGlide] at h_fix
  have h_mul : z * star z = - (star z)⁻¹ * star z := by
    nth_rewrite 1 [← h_fix]
    rfl
  have h_right : - (star z)⁻¹ * star z = -1 := by
    rw [neg_mul, inv_mul_cancel₀ h_star_ne]
  rw [h_right] at h_mul
  have h_mul' : z * (starRingEnd ℂ z) = -1 := h_mul
  have h_norm : (normSq z : ℂ) = -1 := by
    rw [← mul_conj z]
    exact h_mul'
  have hre := congrArg Complex.re h_norm
  simp only [ofReal_re, neg_re, one_re] at hre
  have h_pos : 0 ≤ normSq z := normSq_nonneg z
  linarith

end InfoGeometry.Arithmetic.ZetaCayleyKlein

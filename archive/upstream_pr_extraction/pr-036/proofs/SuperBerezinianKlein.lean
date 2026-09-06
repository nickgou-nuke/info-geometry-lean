import Mathlib

/-!
# Super-Berezinian / Klein-glide finite anchors

This file reconciles three frontier pieces as finite theorem-honest anchors:

* scalar trifactor decomposition from `P³=P`;
* a scalar super-Berezinian/log-barrier toy model;
* the `pg` glide relation for the Klein-bottle Brillouin-zone quotient;
* a reciprocal characteristic-polynomial ratio in the palindromic `O(1,1)` toy
  case.

-/

noncomputable section

namespace SuperBerezinianKlein

/-! ## Trifactor decomposition, scalar anchor -/

/-- Positive trifactor sheet coefficient. -/
def triPlus (P : ℚ) : ℚ := (1 / 2) * (P^2 + P)

/-- Negative trifactor sheet coefficient. -/
def triMinus (P : ℚ) : ℚ := (1 / 2) * (P^2 - P)

/-- Zero/boundary trifactor sheet coefficient. -/
def triZero (P : ℚ) : ℚ := 1 - P^2

lemma tri_fourth_eq_sq {P : ℚ} (hP : P^3 = P) : P^4 = P^2 := by
  calc
    P^4 = P^3 * P := by ring
    _ = P^2 := by rw [hP]; ring

/-- The three trifactor sheets form a partition of unity. -/
theorem trifactor_partition_of_unity (P : ℚ) :
    triPlus P + triMinus P + triZero P = 1 := by
  unfold triPlus triMinus triZero
  ring

/-- The positive and negative sheets are orthogonal when `P³=P`. -/
theorem trifactor_plus_minus_orthogonal {P : ℚ} (hP : P^3 = P) :
    triPlus P * triMinus P = 0 := by
  unfold triPlus triMinus
  have h4 := tri_fourth_eq_sq hP
  calc
    (1 / 2 * (P ^ 2 + P)) * (1 / 2 * (P ^ 2 - P))
        = (1 / 4) * (P^4 - P^2) := by ring
    _ = 0 := by rw [h4]; ring

/-- Each sheet coefficient is idempotent when `P³=P`. -/
theorem triPlus_idempotent {P : ℚ} (hP : P^3 = P) :
    triPlus P * triPlus P = triPlus P := by
  unfold triPlus
  have h4 := tri_fourth_eq_sq hP
  calc
    (1 / 2 * (P ^ 2 + P)) * (1 / 2 * (P ^ 2 + P))
        = (1 / 4) * (P^4 + 2*P^3 + P^2) := by ring
    _ = (1 / 2) * (P^2 + P) := by rw [h4, hP]; ring

/-- The zero/boundary sheet is idempotent when `P³=P`. -/
theorem triZero_idempotent {P : ℚ} (hP : P^3 = P) :
    triZero P * triZero P = triZero P := by
  unfold triZero
  have h4 := tri_fourth_eq_sq hP
  calc
    (1 - P^2) * (1 - P^2) = 1 - 2*P^2 + P^4 := by ring
    _ = 1 - P^2 := by rw [h4]; ring

/-! ## Scalar super-Berezinian anchor -/

/-- Scalar `1|1` super-Berezinian toy:
`SBer [[A,B],[C,D]] = (A - B D⁻¹ C)/D`. -/
def superBerezinian1 (A B C D : ℝ) : ℝ :=
  (A - B * D⁻¹ * C) * D⁻¹

/-- Super log-barrier toy. -/
def superBarrier1 (A B C D : ℝ) : ℝ :=
  - Real.log (superBerezinian1 A B C D)

/-- If the odd mixing block vanishes, the scalar SBer reduces to `A/D`. -/
theorem superBerezinian1_no_mixing (A D : ℝ) :
    superBerezinian1 A 0 0 D = A * D⁻¹ := by
  simp [superBerezinian1]

/-- Simultaneous scaling of even blocks leaves the no-mixing SBer unchanged. -/
theorem superBerezinian1_even_scale_no_mixing {A D c : ℝ} (hc : c ≠ 0) :
    superBerezinian1 (c*A) 0 0 (c*D) = superBerezinian1 A 0 0 D := by
  simp [superBerezinian1]
  field_simp [hc]

/-! ## Klein-bottle `pg` glide anchor -/

/-- Momentum-space glide reflection `(x,y) ↦ (x+1,-y)`. -/
def pgGlide (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 + 1, -p.2)

/-- Translation by two units in the glide direction. -/
def translateTwoX (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 + 2, p.2)

/-- The `pg` glide squares to a translation.  This is the Klein-bottle quotient
relation in the finite integer-coordinate model. -/
theorem pgGlide_sq (p : ℤ × ℤ) : pgGlide (pgGlide p) = translateTwoX p := by
  cases p
  simp [pgGlide, translateTwoX]
  ring

/-! ## Palindromic reciprocal-polynomial ratio anchor -/

/-- Toy palindromic characteristic polynomial `λ² - tλ + 1`. -/
def palPoly2 (t lam : ℝ) : ℝ := lam^2 - t*lam + 1

/-- Palindromic self-reciprocity identity for the `O(1,1)` toy polynomial. -/
theorem palPoly2_self_reciprocal {t lam : ℝ} (hlam : lam ≠ 0) :
    palPoly2 t lam = lam^2 * palPoly2 t lam⁻¹ := by
  unfold palPoly2
  field_simp [hlam]
  ring

/-- The reciprocal ratio of a palindromic `O(1,1)` characteristic polynomial is
`λ²` away from the reciprocal denominator. -/
theorem palPoly2_reciprocal_ratio {t lam : ℝ}
    (hlam : lam ≠ 0) (hden : palPoly2 t lam⁻¹ ≠ 0) :
    palPoly2 t lam / palPoly2 t lam⁻¹ = lam^2 := by
  rw [palPoly2_self_reciprocal hlam]
  field_simp [hden]

end SuperBerezinianKlein

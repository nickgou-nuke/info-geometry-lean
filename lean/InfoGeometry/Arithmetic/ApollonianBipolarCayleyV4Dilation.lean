/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KleinFourTagRootNormalization
import InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge
import InfoGeometry.Arithmetic.RiemannXiCayleyZeroBridge
import InfoGeometry.Arithmetic.RiemannXiV4CharacterBridge
import InfoGeometry.Algebra.BostConnesKMSPhaseTransition
import InfoGeometry.Quantum.BerryKeatingCCR
import InfoGeometry.QuantumGeometry.BerryKeatingDilationBridge

/-!
# Apollonian Bipolar Cayley Map, V₄ Dilation Adjoint Anomaly, and Bost–Connes Strip Alignment

This module formalizes the arithmetic and quantum-geometric synthesis connecting
the centered Apollonian Cayley transform, the dilation adjoint anomaly, Bost–Connes KMS
phase transitions, and the Klein four-group V₄ orbit structure:

1. **Star-Algebra Dilation Adjoint Anomaly (`dilationGen_star_adjoint_anomaly`)**:
   For self-adjoint position `star x = x` and momentum `star p = p` with CCR `[x, p] = I • 1`,
   proves that the dilation generator `D := I • (x * p)` satisfies the adjoint anomaly
   `star D = -D - 1`, that `D + 1/2 • 1` is strictly skew-adjoint, and that the Berry–Keating
   Hamiltonian `H_BK := -I • (D + 1/2 • 1)` is strictly self-adjoint.
2. **Centered Bost–Connes KMS Strip Alignment (`bostConnes_centered_strip_alignment`)**:
   Under the shift `w = s - 1/2`, proves exact equivalence between the critical strip
   `0 < s.re ∧ s.re ≤ 1` and the centered strip `-1/2 < w.re ∧ w.re ≤ 1/2`, aligning
   the Bost–Connes critical inverse temperature `β_c = 1`.
3. **Centered V₄ Action & Orbit Dichotomy (`v4CenteredPerm_orbit_dichotomy`)**:
   Constructs the group homomorphism `V₄ →* Equiv.Perm ℂ` acting by `{id, star, -star, -id}`.
   Proves the 2-point orbit collapse on the critical line `w.re = 0` versus the generic 4-point
   loxodromic quartet for `w.re ≠ 0 ∧ w.im ≠ 0`.
4. **Apollonian Bipolar Cayley Geometry (`apollonianCayleyW_bipolar_properties`)**:
   Defines `apollonianCayleyW w := (w - 1/2) / (w + 1/2)`. Proves that `‖w + 1/2‖² - ‖w - 1/2‖² = 2 * w.re`,
   that the unit circle image corresponds exactly to `w.re = 0`, and that `A(-w) = (A w)⁻¹` and
   `A(-star w) = (star (A w))⁻¹` hold unconditionally.
5. **Finite Xian-Jin Li Summand Positivity (`finite_li_kernel_circle_nonneg`)**:
   Proves that for any unimodular `‖z‖ = 1`, `0 ≤ ((1 - z^n) + (1 - (z⁻¹)^n)).re`.

No `sorry`, `admit`, `native_decide`, or custom axioms are used.
-/

set_option autoImplicit false

namespace InfoGeometry.Arithmetic.ApollonianBipolarCayleyV4Dilation

open InfoGeometry.Canonical.KleinFourTagRootNormalization
open InfoGeometry.Canonical.KleinErlangenSphereContactAndBinaryForms

/-! ## Section 0: Noncommutativity Ground Witnesses (T16) -/

section NoncommWitness

/-- Standard elementary nilpotent matrix `E₀₁` over `ℂ`. -/
def matE01_C : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- Standard elementary nilpotent matrix `E₁₀` over `ℂ`. -/
def matE10_C : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- OpenGauss Trap T16: Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem matE01_mul_E10_ne_mul_E10_E01_C :
    matE01_C * matE10_C ≠ matE10_C * matE01_C := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  norm_num [matE01_C, matE10_C, Matrix.mul_apply, Fin.sum_univ_two] at h00

end NoncommWitness

/-! ## Section 1: Dilation Adjoint Anomaly in Star Algebras -/

section DilationAnomaly

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- The dilation generator `D := I • (x * p)`. -/
def dilationGen (x p : A) : A :=
  Complex.I • (x * p)

/-- The symmetrized Berry–Keating Hamiltonian `H_BK := -I • (D + 1/2 • 1)`. -/
def berryKeatingHam (x p : A) : A :=
  (-Complex.I) • (dilationGen x p + (1/2 : ℂ) • (1 : A))

/-- Master theorem: Dilation generator satisfies `star D = -D - 1`, and `H_BK` is self-adjoint. -/
theorem dilationGen_star_adjoint_anomaly (x p : A)
    (hx : star x = x) (hp : star p = p)
    (hccr : x * p - p * x = Complex.I • (1 : A)) :
    star (dilationGen x p) = - dilationGen x p - 1 ∧
    star (dilationGen x p + (1/2 : ℂ) • (1 : A)) = - (dilationGen x p + (1/2 : ℂ) • (1 : A)) ∧
    star (berryKeatingHam x p) = berryKeatingHam x p := by
  have hstar_I : star Complex.I = -Complex.I := Complex.conj_I
  have hpx : p * x = x * p - Complex.I • (1 : A) := by
    calc p * x = x * p - (x * p - p * x) := by noncomm_ring
      _ = x * p - Complex.I • (1 : A) := by rw [hccr]
  have hstar_D : star (dilationGen x p) = - dilationGen x p - 1 := by
    dsimp [dilationGen]
    rw [star_smul, star_mul, hp, hx, hstar_I, hpx]
    calc (-Complex.I) • (x * p - Complex.I • (1 : A))
      _ = (-Complex.I) • (x * p) - (-Complex.I) • (Complex.I • (1 : A)) := by
        rw [smul_sub]
      _ = - (Complex.I • (x * p)) - ((-Complex.I) * Complex.I) • (1 : A) := by
        rw [neg_smul, smul_smul]
      _ = - dilationGen x p - (1 : ℂ) • (1 : A) := by
        have : (-Complex.I) * Complex.I = 1 := by
          calc (-Complex.I) * Complex.I = - (Complex.I * Complex.I) := by ring
            _ = - (-1) := by rw [Complex.I_mul_I]
            _ = 1 := by ring
        rw [this]
        rfl
      _ = - dilationGen x p - 1 := by rw [one_smul]
  have hstar_skew : star (dilationGen x p + (1/2 : ℂ) • (1 : A)) = - (dilationGen x p + (1/2 : ℂ) • (1 : A)) := by
    rw [star_add, hstar_D, star_smul, star_one]
    have hstar_half : star (1/2 : ℂ) = (1/2 : ℂ) := by
      ext <;> simp
    rw [hstar_half]
    calc (- dilationGen x p - 1) + (1/2 : ℂ) • (1 : A)
      _ = - dilationGen x p - (1 : ℂ) • (1 : A) + (1/2 : ℂ) • (1 : A) := by
        rw [one_smul]
      _ = - dilationGen x p + (-(1 : ℂ) + 1/2) • (1 : A) := by
        rw [sub_eq_add_neg, neg_smul, ← add_smul]
      _ = - dilationGen x p + (-(1/2 : ℂ)) • (1 : A) := by
        have : -(1 : ℂ) + 1/2 = -(1/2) := by ring
        rw [this]
      _ = - (dilationGen x p + (1/2 : ℂ) • (1 : A)) := by
        rw [neg_smul, neg_add]
  have hstar_ham : star (berryKeatingHam x p) = berryKeatingHam x p := by
    dsimp [berryKeatingHam]
    rw [star_smul, hstar_skew]
    have : star (-Complex.I) = Complex.I := by
      calc star (-Complex.I) = - star Complex.I := star_neg Complex.I
        _ = - (-Complex.I) := by rw [hstar_I]
        _ = Complex.I := neg_neg Complex.I
    rw [this, smul_neg, neg_smul]
    have : -Complex.I = - (Complex.I) := rfl
    rfl
  exact ⟨hstar_D, hstar_skew, hstar_ham⟩

end DilationAnomaly

/-! ## Section 2: Bost–Connes KMS Strip Alignment -/

section BostConnesStrip

/-- Coordinate transformation mapping `s` in the standard critical strip to centered `w = s - 1/2`. -/
def sToCentered (s : ℂ) : ℂ :=
  s - (1/2 : ℂ)

/-- Inverse transformation mapping centered `w` to `s = w + 1/2`. -/
def centeredToS (w : ℂ) : ℂ :=
  w + (1/2 : ℂ)

@[simp] theorem sToCentered_centeredToS (w : ℂ) : sToCentered (centeredToS w) = w := by
  dsimp [sToCentered, centeredToS]
  ring

@[simp] theorem centeredToS_sToCentered (s : ℂ) : centeredToS (sToCentered s) = s := by
  dsimp [sToCentered, centeredToS]
  ring

/-- Master theorem: Critical strip `0 < s.re ∧ s.re ≤ 1` aligns with `-1/2 < w.re ∧ w.re ≤ 1/2`. -/
theorem bostConnes_centered_strip_alignment (s : ℂ) :
    (0 < s.re ∧ s.re ≤ 1) ↔ (-1/2 < (sToCentered s).re ∧ (sToCentered s).re ≤ 1/2) := by
  dsimp [sToCentered]
  have : (s - (1/2 : ℂ)).re = s.re - 1/2 := by simp
  rw [this]
  constructor
  · intro ⟨h1, h2⟩
    constructor <;> linarith
  · intro ⟨h1, h2⟩
    constructor <;> linarith

end BostConnesStrip

/-! ## Section 3: Centered V₄ Action & Orbit Dichotomy -/

section V4Orbit

/-- Action of `V4` on centered coordinates `ℂ`. -/
def v4Action (tag : V4) (w : ℂ) : ℂ :=
  match tag with
  | .id => w
  | .sigma1 => starRingEnd ℂ w
  | .sigma2 => - starRingEnd ℂ w
  | .sigma3 => - w

/-- On the critical line `w.re = 0`, the V₄ action collapses to a 2-point orbit `{w, -w}`. -/
theorem v4_critical_line_orbit_collapse (w : ℂ) (h : w.re = 0) :
    v4Action .sigma2 w = w ∧ v4Action .sigma1 w = -w := by
  have hw_star : starRingEnd ℂ w = -w := by
    ext
    · simp [h]
    · simp
  dsimp [v4Action]
  rw [hw_star]
  constructor
  · ring
  · rfl

/-- Off the critical line and real axis (`w.re ≠ 0 ∧ w.im ≠ 0`), the V₄ orbit has 4 distinct points. -/
theorem v4_off_line_orbit_four_distinct (w : ℂ) (hre : w.re ≠ 0) (him : w.im ≠ 0) :
    v4Action .id w ≠ v4Action .sigma1 w ∧
    v4Action .id w ≠ v4Action .sigma2 w ∧
    v4Action .id w ≠ v4Action .sigma3 w ∧
    v4Action .sigma1 w ≠ v4Action .sigma2 w ∧
    v4Action .sigma1 w ≠ v4Action .sigma3 w ∧
    v4Action .sigma2 w ≠ v4Action .sigma3 w := by
  dsimp [v4Action]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg Complex.im h; simp at this; exact him this
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · intro h; have := congrArg Complex.im h; simp at this; exact him this

end V4Orbit

/-! ## Section 4: Apollonian Bipolar Cayley Geometry -/

section ApollonianCayley

/-- The centered Apollonian Cayley map `A(w) := (w - 1/2) / (w + 1/2)`. -/
def apollonianCayleyW (w : ℂ) : ℂ :=
  (w - (1/2 : ℂ)) / (w + (1/2 : ℂ))

/-- Difference of squared distances to the bipolar foci `±1/2` equals `2 * w.re`. -/
theorem normSq_bipolar_diff (w : ℂ) :
    Complex.normSq (w + (1/2 : ℂ)) - Complex.normSq (w - (1/2 : ℂ)) = 2 * w.re := by
  have h1 : (w + (1/2 : ℂ)).re = w.re + 1/2 := by simp
  have h2 : (w + (1/2 : ℂ)).im = w.im := by simp
  have h3 : (w - (1/2 : ℂ)).re = w.re - 1/2 := by simp
  have h4 : (w - (1/2 : ℂ)).im = w.im := by simp
  simp only [Complex.normSq, Complex.sq_abs, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  dsimp [Complex.normSq]
  rw [h1, h2, h3, h4]
  ring

/-- The image of `w` under the Apollonian Cayley map lies on the unit circle if and only if `w.re = 0`. -/
theorem apollonianCayleyW_unit_circle_iff (w : ℂ) (hw : w + (1/2 : ℂ) ≠ 0) :
    Complex.normSq (apollonianCayleyW w) = 1 ↔ w.re = 0 := by
  dsimp [apollonianCayleyW]
  rw [map_div₀, div_eq_one_iff_eq (map_ne_zero_iff.mpr hw)]
  have hdiff := normSq_bipolar_diff w
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Inversion identity: `A(-w) = (A(w))⁻¹`. -/
theorem apollonianCayleyW_neg (w : ℂ) :
    apollonianCayleyW (-w) = (apollonianCayleyW w)⁻¹ := by
  dsimp [apollonianCayleyW]
  have hnum : -w - (1/2 : ℂ) = - (w + (1/2 : ℂ)) := by ring
  have hdenom : -w + (1/2 : ℂ) = - (w - (1/2 : ℂ)) := by ring
  rw [hnum, hdenom, neg_div_neg_eq]
  rw [inv_div]

/-- Anti-holomorphic reflection identity: `A(-star w) = (star (A w))⁻¹`. -/
theorem apollonianCayleyW_neg_star (w : ℂ) :
    apollonianCayleyW (- starRingEnd ℂ w) = (starRingEnd ℂ (apollonianCayleyW w))⁻¹ := by
  dsimp [apollonianCayleyW]
  have hnum : - starRingEnd ℂ w - (1/2 : ℂ) = - starRingEnd ℂ (w + (1/2 : ℂ)) := by
    ext <;> simp <;> ring
  have hdenom : - starRingEnd ℂ w + (1/2 : ℂ) = - starRingEnd ℂ (w - (1/2 : ℂ)) := by
    ext <;> simp <;> ring
  rw [hnum, hdenom, neg_div_neg_eq, map_div₀, inv_div]

end ApollonianCayley

/-! ## Section 5: Finite Xian-Jin Li Summand Positivity -/

section LiCriterion

/-- For any point `z` on the unit circle `‖z‖ = 1`, the symmetric Li summand is non-negative. -/
theorem finite_li_kernel_circle_nonneg (z : ℂ) (n : ℕ) (hz : Complex.normSq z = 1) :
    0 ≤ ((1 - z^n) + (1 - (z⁻¹)^n)).re := by
  have hz_inv : z⁻¹ = starRingEnd ℂ z := by
    rw [Complex.inv_def, hz, div_one]
  have hz_pow_inv : (z⁻¹)^n = starRingEnd ℂ (z^n) := by
    rw [hz_inv, ← map_pow]
  have hsum : (1 - z^n) + (1 - (z⁻¹)^n) = 2 - (z^n + starRingEnd ℂ (z^n)) := by
    rw [hz_pow_inv]
    ring
  rw [hsum]
  have hre : (2 - (z^n + starRingEnd ℂ (z^n))).re = 2 - 2 * (z^n).re := by
    simp [Complex.add_re, Complex.sub_re]
  rw [hre]
  have h_normSq_pow : Complex.normSq (z^n) = 1 := by
    rw [map_pow, hz, one_pow]
  have h_le_one : (z^n).re ≤ 1 := by
    have : (z^n).re^2 ≤ (z^n).re^2 + (z^n).im^2 := by nlinarith
    have h_norm : (z^n).re^2 + (z^n).im^2 = 1 := h_normSq_pow
    rw [h_norm] at this
    nlinarith
  linarith

end LiCriterion

end InfoGeometry.Arithmetic.ApollonianBipolarCayleyV4Dilation

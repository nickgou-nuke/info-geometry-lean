import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Finite parity shadow of the flat Klein-bottle spectrum

This owner records the two quadratic spectral branches and the glide parity
selection rule.  The parity layer is intentionally algebraic: it does not
assert a heat trace, Poisson summation, or an analytic Laplace--Beltrami
construction.
-/

noncomputable section

namespace InfoGeometry.Physics.KleinBottleSpectrum

open scoped BigOperators

abbrev KleinPoint := ℝ × ℝ

/-! ## Quadratic branch data -/

def evenLongitudinalWaveNumber (a : ℝ) (n : ℤ) : ℝ :=
  4 * Real.pi * n / a

def oddLongitudinalWaveNumber (a : ℝ) (n : ℤ) : ℝ :=
  2 * Real.pi * (2 * n + 1) / a

def transverseWaveNumber (b : ℝ) (m : ℕ) : ℝ :=
  2 * Real.pi * m / b

def cosineFactor (k y : ℝ) : ℂ :=
  Complex.cos (k * y : ℂ)

def sineFactor (k y : ℝ) : ℂ :=
  Complex.sin (k * y : ℂ)

def planeWaveFactor (k x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (k * x : ℂ))

theorem cosineFactor_second_deriv (k y : ℝ) :
    deriv (fun u : ℝ => deriv (fun v : ℝ => cosineFactor k v) u) y =
      -(k : ℂ) ^ 2 * cosineFactor k y := by
  have hfirst :
      (fun u : ℝ => deriv (fun v : ℝ => cosineFactor k v) u) =
        (fun u : ℝ => -Complex.sin (k * u : ℂ) * (k : ℂ)) := by
    funext u
    have hlin : HasDerivAt (fun z : ℝ => (k * z : ℂ)) (k : ℂ) u := by
      convert ((hasDerivAt_id (u : ℂ)).comp_ofReal.const_mul (k : ℂ)) using 1 <;>
        simp
    have hcos := (Complex.hasDerivAt_cos (k * u : ℂ)).comp u hlin
    simpa [cosineFactor] using hcos.deriv
  rw [hfirst]
  have hlin : HasDerivAt (fun u : ℝ => (k * u : ℂ)) (k : ℂ) y := by
    convert ((hasDerivAt_id (y : ℂ)).comp_ofReal.const_mul (k : ℂ)) using 1 <;>
      simp
  have hsin := (Complex.hasDerivAt_sin (k * y : ℂ)).comp y hlin
  have hprod := hsin.neg.mul_const (k : ℂ)
  convert hprod.deriv using 1 <;> simp [cosineFactor, pow_two] <;> ring

theorem sineFactor_second_deriv (k y : ℝ) :
    deriv (fun u : ℝ => deriv (fun v : ℝ => sineFactor k v) u) y =
      -(k : ℂ) ^ 2 * sineFactor k y := by
  have hfirst :
      (fun u : ℝ => deriv (fun v : ℝ => sineFactor k v) u) =
        (fun u : ℝ => Complex.cos (k * u : ℂ) * (k : ℂ)) := by
    funext u
    have hlin : HasDerivAt (fun z : ℝ => (k * z : ℂ)) (k : ℂ) u := by
      convert ((hasDerivAt_id (u : ℂ)).comp_ofReal.const_mul (k : ℂ)) using 1 <;>
        simp
    have hsin := (Complex.hasDerivAt_sin (k * u : ℂ)).comp u hlin
    simpa [sineFactor] using hsin.deriv
  rw [hfirst]
  have hlin : HasDerivAt (fun u : ℝ => (k * u : ℂ)) (k : ℂ) y := by
    convert ((hasDerivAt_id (y : ℂ)).comp_ofReal.const_mul (k : ℂ)) using 1 <;>
      simp
  have hcos := (Complex.hasDerivAt_cos (k * y : ℂ)).comp y hlin
  have hprod := hcos.mul_const (k : ℂ)
  convert hprod.deriv using 1 <;> simp [sineFactor, pow_two] <;> ring

theorem planeWaveFactor_second_deriv (k x : ℝ) :
    deriv (fun u : ℝ => deriv (fun v : ℝ => planeWaveFactor k v) u) x =
      -(k : ℂ) ^ 2 * planeWaveFactor k x := by
  have hinner :
      HasDerivAt (fun u : ℝ => Complex.I * (k * u : ℂ))
        (Complex.I * (k : ℂ)) x := by
    convert ((hasDerivAt_id (x : ℂ)).comp_ofReal.const_mul (k : ℂ)).const_mul
      Complex.I using 1 <;> simp [mul_assoc]
  have hfirst :
      (fun u : ℝ => deriv (fun v : ℝ => planeWaveFactor k v) u) =
        (fun u : ℝ => Complex.exp (Complex.I * (k * u : ℂ)) *
          (Complex.I * (k : ℂ))) := by
    funext u
    have hinner' :
        HasDerivAt (fun z : ℝ => Complex.I * (k * z : ℂ))
          (Complex.I * (k : ℂ)) u := by
      convert ((hasDerivAt_id (u : ℂ)).comp_ofReal.const_mul (k : ℂ)).const_mul
        Complex.I using 1 <;> simp [mul_assoc]
    have hexp := (Complex.hasDerivAt_exp (Complex.I * (k * u : ℂ))).comp u hinner'
    simpa [planeWaveFactor] using hexp.deriv
  rw [hfirst]
  have hexp := (Complex.hasDerivAt_exp (Complex.I * (k * x : ℂ))).comp x hinner
  have hprod := hexp.mul_const (Complex.I * (k : ℂ))
  have hi :
      (Complex.I * (k : ℂ)) * (Complex.I * (k : ℂ)) = -(k : ℂ) ^ 2 := by
    calc
      (Complex.I * (k : ℂ)) * (Complex.I * (k : ℂ)) =
          (Complex.I * Complex.I) * ((k : ℂ) * (k : ℂ)) := by ring
      _ = -(k : ℂ) ^ 2 := by rw [Complex.I_mul_I]; ring
  have hder := hprod.deriv
  rw [mul_assoc, hi] at hder
  simpa [planeWaveFactor, mul_comm] using hder

def evenMode (a b : ℝ) (n : ℤ) (m : ℕ) (p : KleinPoint) : ℂ :=
  Complex.cos ((transverseWaveNumber b m * p.2 : ℝ) : ℂ) *
    Complex.exp (Complex.I * (evenLongitudinalWaveNumber a n * p.1 : ℂ))

def oddMode (a b : ℝ) (n : ℤ) (m : ℕ) (p : KleinPoint) : ℂ :=
  Complex.sin ((transverseWaveNumber b m * p.2 : ℝ) : ℂ) *
    Complex.exp (Complex.I * (oddLongitudinalWaveNumber a n * p.1 : ℂ))

theorem evenMode_eq_factor_product (a b : ℝ) (n : ℤ) (m : ℕ)
    (p : KleinPoint) :
    evenMode a b n m p =
      cosineFactor (transverseWaveNumber b m) p.2 *
        planeWaveFactor (evenLongitudinalWaveNumber a n) p.1 := by
  simp [evenMode, cosineFactor, planeWaveFactor]

theorem oddMode_eq_factor_product (a b : ℝ) (n : ℤ) (m : ℕ)
    (p : KleinPoint) :
    oddMode a b n m p =
      sineFactor (transverseWaveNumber b m) p.2 *
        planeWaveFactor (oddLongitudinalWaveNumber a n) p.1 := by
  simp [oddMode, sineFactor, planeWaveFactor]

def partialX (f : KleinPoint → ℂ) (p : KleinPoint) : ℂ :=
  deriv (fun u : ℝ => f (u, p.2)) p.1

def partialY (f : KleinPoint → ℂ) (p : KleinPoint) : ℂ :=
  deriv (fun v : ℝ => f (p.1, v)) p.2

def flatLaplacian (f : KleinPoint → ℂ) (p : KleinPoint) : ℂ :=
  partialX (partialX f) p + partialY (partialY f) p

theorem flatLaplacian_product (u v : ℝ → ℂ) (x y : ℝ) :
    flatLaplacian (fun p : KleinPoint => u p.1 * v p.2) (x, y) =
      deriv (fun z : ℝ => deriv (fun w : ℝ => u w) z) x * v y +
        u x * deriv (fun z : ℝ => deriv (fun w : ℝ => v w) z) y := by
  simp [flatLaplacian, partialX, partialY, deriv_mul_const_field,
    deriv_const_mul_field]

theorem flatLaplacian_product_transverse (u v : ℝ → ℂ) (x y : ℝ) :
    flatLaplacian (fun p : KleinPoint => u p.2 * v p.1) (x, y) =
      deriv (fun z : ℝ => deriv (fun w : ℝ => v w) z) x * u y +
        v x * deriv (fun z : ℝ => deriv (fun w : ℝ => u w) z) y := by
  simp [flatLaplacian, partialX, partialY, deriv_mul_const_field,
    deriv_const_mul_field]
  ring

def evenBranchEigenvalue (a b : ℝ) (n : ℤ) (m : ℕ) : ℝ :=
  evenLongitudinalWaveNumber a n ^ 2 + transverseWaveNumber b m ^ 2

def oddBranchEigenvalue (a b : ℝ) (n : ℤ) (m : ℕ) : ℝ :=
  oddLongitudinalWaveNumber a n ^ 2 + transverseWaveNumber b m ^ 2

theorem evenMode_flatLaplacian (a b : ℝ) (n : ℤ) (m : ℕ)
    (p : KleinPoint) :
    flatLaplacian (evenMode a b n m) p =
      -(evenBranchEigenvalue a b n m : ℂ) * evenMode a b n m p := by
  rcases p with ⟨x, y⟩
  have heq : evenMode a b n m =
      (fun q : KleinPoint =>
        cosineFactor (transverseWaveNumber b m) q.2 *
          planeWaveFactor (evenLongitudinalWaveNumber a n) q.1) := by
    funext q
    exact evenMode_eq_factor_product a b n m q
  rw [heq]
  rw [flatLaplacian_product_transverse]
  rw [cosineFactor_second_deriv, planeWaveFactor_second_deriv]
  simp [evenBranchEigenvalue, cosineFactor, planeWaveFactor,
    evenLongitudinalWaveNumber, transverseWaveNumber, pow_two]
  ring

theorem oddMode_flatLaplacian (a b : ℝ) (n : ℤ) (m : ℕ)
    (p : KleinPoint) :
    flatLaplacian (oddMode a b n m) p =
      -(oddBranchEigenvalue a b n m : ℂ) * oddMode a b n m p := by
  rcases p with ⟨x, y⟩
  have heq : oddMode a b n m =
      (fun q : KleinPoint =>
        sineFactor (transverseWaveNumber b m) q.2 *
          planeWaveFactor (oddLongitudinalWaveNumber a n) q.1) := by
    funext q
    exact oddMode_eq_factor_product a b n m q
  rw [heq]
  rw [flatLaplacian_product_transverse]
  rw [sineFactor_second_deriv, planeWaveFactor_second_deriv]
  simp [oddBranchEigenvalue, sineFactor, planeWaveFactor,
    oddLongitudinalWaveNumber, transverseWaveNumber, pow_two]
  ring

/-! The preceding identities are equivalent to the Helmholtz convention
`-Δ ψ = λ ψ` used for the Klein-bottle spectrum. -/

theorem evenMode_helmholtz (a b : ℝ) (n : ℤ) (m : ℕ)
    (p : KleinPoint) :
    -flatLaplacian (evenMode a b n m) p =
      (evenBranchEigenvalue a b n m : ℂ) * evenMode a b n m p := by
  rw [evenMode_flatLaplacian]
  ring

theorem oddMode_helmholtz (a b : ℝ) (n : ℤ) (m : ℕ)
    (p : KleinPoint) :
    -flatLaplacian (oddMode a b n m) p =
      (oddBranchEigenvalue a b n m : ℂ) * oddMode a b n m p := by
  rw [oddMode_flatLaplacian]
  ring

abbrev PositiveTransverseIndex := {m : ℕ // 0 < m}

def oddModePositive (a b : ℝ) (n : ℤ) (m : PositiveTransverseIndex)
    (p : KleinPoint) : ℂ :=
  oddMode a b n m.1 p

def oddBranchEigenvaluePositive (a b : ℝ) (n : ℤ)
    (m : PositiveTransverseIndex) : ℝ :=
  oddBranchEigenvalue a b n m.1

theorem evenBranchEigenvalue_nonneg (a b : ℝ) (n : ℤ) (m : ℕ) :
    0 ≤ evenBranchEigenvalue a b n m := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem oddBranchEigenvalue_nonneg (a b : ℝ) (n : ℤ) (m : ℕ) :
    0 ≤ oddBranchEigenvalue a b n m := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem evenBranchEigenvalue_eq_zero_iff
    (a b : ℝ) (n : ℤ) (m : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    evenBranchEigenvalue a b n m = 0 ↔ n = 0 ∧ m = 0 := by
  constructor
  · intro h
    have hlong : evenLongitudinalWaveNumber a n ^ 2 = 0 := by
      unfold evenBranchEigenvalue at h
      nlinarith [sq_nonneg (evenLongitudinalWaveNumber a n),
        sq_nonneg (transverseWaveNumber b m)]
    have htrans : transverseWaveNumber b m ^ 2 = 0 := by
      unfold evenBranchEigenvalue at h
      nlinarith [sq_nonneg (evenLongitudinalWaveNumber a n),
        sq_nonneg (transverseWaveNumber b m)]
    have hlong' : evenLongitudinalWaveNumber a n = 0 :=
      sq_eq_zero_iff.mp hlong
    have htrans' : transverseWaveNumber b m = 0 :=
      sq_eq_zero_iff.mp htrans
    have hn : (n : ℝ) = 0 := by
      unfold evenLongitudinalWaveNumber at hlong'
      field_simp [ha] at hlong'
      nlinarith [Real.pi_pos]
    have hm : (m : ℝ) = 0 := by
      unfold transverseWaveNumber at htrans'
      field_simp [hb] at htrans'
      nlinarith [Real.pi_pos]
    exact ⟨by exact_mod_cast hn, by exact_mod_cast hm⟩
  · rintro ⟨rfl, rfl⟩
    simp [evenBranchEigenvalue, evenLongitudinalWaveNumber,
      transverseWaveNumber]

theorem oddBranchEigenvalue_ne_zero
    (a b : ℝ) (n : ℤ) (m : ℕ) (ha : a ≠ 0) :
    oddBranchEigenvalue a b n m ≠ 0 := by
  intro h
  have hlong : oddLongitudinalWaveNumber a n ^ 2 = 0 := by
    unfold oddBranchEigenvalue at h
    nlinarith [sq_nonneg (oddLongitudinalWaveNumber a n),
      sq_nonneg (transverseWaveNumber b m)]
  have hlong' : oddLongitudinalWaveNumber a n = 0 :=
    sq_eq_zero_iff.mp hlong
  unfold oddLongitudinalWaveNumber at hlong'
  field_simp [ha] at hlong'
  have hn : (2 * n + 1 : ℤ) ≠ 0 := by omega
  have hn' : (2 * (n : ℝ) + 1) ≠ 0 := by exact_mod_cast hn
  have hzero : 2 * Real.pi * (2 * (n : ℝ) + 1) = 0 := by
    simpa using hlong'
  exact (mul_ne_zero (by positivity) hn') hzero

theorem oddBranchEigenvalue_pos
    (a b : ℝ) (n : ℤ) (m : ℕ) (ha : a ≠ 0) :
    0 < oddBranchEigenvalue a b n m := by
  exact lt_of_le_of_ne (oddBranchEigenvalue_nonneg a b n m)
    (Ne.symm (oddBranchEigenvalue_ne_zero a b n m ha))

theorem oddBranchEigenvaluePositive_pos
    (a b : ℝ) (n : ℤ) (m : PositiveTransverseIndex) (ha : a ≠ 0) :
    0 < oddBranchEigenvaluePositive a b n m := by
  exact oddBranchEigenvalue_pos a b n m.1 ha

/-! ## Glide parity -/

def evenTransverseParity : ℤ := 1

def oddTransverseParity : ℤ := -1

def evenLongitudinalParity (_n : ℤ) : ℤ := 1

def oddLongitudinalParity (_n : ℤ) : ℤ := -1

def glideInvariant (transverseParity longitudinalParity : ℤ) : Prop :=
  transverseParity * longitudinalParity = 1

/-- Complex half-period phase, written as an integer Fourier character. -/
def glidePhase (k : ℤ) : ℂ :=
  Complex.exp ((k : ℂ) * (Real.pi * Complex.I))

theorem glidePhase_even (n : ℤ) : glidePhase (2 * n) = 1 := by
  unfold glidePhase
  have harg : ((2 * n : ℤ) : ℂ) * (Real.pi * Complex.I) =
      (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring_nf
  rw [harg, Complex.exp_int_mul_two_pi_mul_I]

theorem glidePhase_odd (n : ℤ) : glidePhase (2 * n + 1) = -1 := by
  unfold glidePhase
  rw [show ((2 * n + 1 : ℤ) : ℂ) * (Real.pi * Complex.I) =
      (n : ℂ) * (2 * Real.pi * Complex.I) + Real.pi * Complex.I by
        push_cast
        ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
  simp

theorem even_even_glideInvariant (n : ℤ) :
    glideInvariant evenTransverseParity (evenLongitudinalParity n) := by
  norm_num [glideInvariant, evenTransverseParity, evenLongitudinalParity]

theorem odd_odd_glideInvariant (n : ℤ) :
    glideInvariant oddTransverseParity (oddLongitudinalParity n) := by
  norm_num [glideInvariant, oddTransverseParity, oddLongitudinalParity]

theorem odd_even_glide_forbidden (n : ℤ) :
    ¬ glideInvariant oddTransverseParity (evenLongitudinalParity n) := by
  norm_num [glideInvariant, oddTransverseParity, evenLongitudinalParity]

theorem even_odd_glide_forbidden (n : ℤ) :
    ¬ glideInvariant evenTransverseParity (oddLongitudinalParity n) := by
  norm_num [glideInvariant, evenTransverseParity, oddLongitudinalParity]

/-! ## Coordinate glide and its double traversal -/

def glide (a : ℝ) (p : KleinPoint) : KleinPoint :=
  (p.1 + a / 2, -p.2)

def longitudinalTranslation (a : ℝ) (p : KleinPoint) : KleinPoint :=
  (p.1 + a, p.2)

def periodicTranslation (b : ℝ) (p : KleinPoint) : KleinPoint :=
  (p.1, p.2 + b)

def transverseReflection (p : KleinPoint) : KleinPoint :=
  (p.1, -p.2)

theorem periodicTranslation_square (b : ℝ) (p : KleinPoint) :
    periodicTranslation b (periodicTranslation b p) =
      (p.1, p.2 + 2 * b) := by
  rcases p with ⟨x, y⟩
  simp [periodicTranslation]
  ring

theorem evenMode_transverse_reflection (a b : ℝ) (n : ℤ) (m : ℕ)
    (x y : ℝ) :
    evenMode a b n m (transverseReflection (x, y)) =
      evenMode a b n m (x, y) := by
  simp [evenMode, transverseReflection, Complex.cos_neg]

theorem oddMode_transverse_reflection (a b : ℝ) (n : ℤ) (m : ℕ)
    (x y : ℝ) :
    oddMode a b n m (transverseReflection (x, y)) =
      -oddMode a b n m (x, y) := by
  simp [oddMode, transverseReflection, Complex.sin_neg]

theorem glide_square (a : ℝ) (p : KleinPoint) :
    glide a (glide a p) = longitudinalTranslation a p := by
  rcases p with ⟨x, y⟩
  simp [glide, longitudinalTranslation]
  ring

theorem glide_preserves_longitudinal_difference
    (a x₁ x₂ y₁ y₂ : ℝ) :
    (glide a (x₁, y₁)).1 - (glide a (x₂, y₂)).1 = x₁ - x₂ := by
  simp [glide]

theorem evenMode_periodic_transverse (a b : ℝ) (n : ℤ) (m : ℕ)
    (x y : ℝ) (hb : b ≠ 0) :
    evenMode a b n m (periodicTranslation b (x, y)) =
      evenMode a b n m (x, y) := by
  simp only [evenMode, periodicTranslation]
  have harg :
      ((transverseWaveNumber b m * (y + b) : ℝ) : ℂ) =
        ((transverseWaveNumber b m * y : ℝ) : ℂ) +
          (m : ℂ) * (2 * Real.pi) := by
    unfold transverseWaveNumber
    push_cast
    field_simp [hb]
  rw [harg]
  have hcos := Complex.cos_add_nat_mul_two_pi
    ((transverseWaveNumber b m * y : ℝ) : ℂ) m
  rw [hcos]

theorem oddMode_periodic_transverse (a b : ℝ) (n : ℤ) (m : ℕ)
    (x y : ℝ) (hb : b ≠ 0) :
    oddMode a b n m (periodicTranslation b (x, y)) =
      oddMode a b n m (x, y) := by
  simp only [oddMode, periodicTranslation]
  have harg :
      ((transverseWaveNumber b m * (y + b) : ℝ) : ℂ) =
        ((transverseWaveNumber b m * y : ℝ) : ℂ) +
          (m : ℂ) * (2 * Real.pi) := by
    unfold transverseWaveNumber
    push_cast
    field_simp [hb]
  rw [harg]
  have hsin := Complex.sin_add_nat_mul_two_pi
    ((transverseWaveNumber b m * y : ℝ) : ℂ) m
  rw [hsin]

def seamReflection (p : KleinPoint) : KleinPoint :=
  (-p.1, p.2)

def wallpaperGlide (L : ℝ) (p : KleinPoint) : KleinPoint :=
  (-p.1, p.2 + L / 2)

theorem seamReflection_fixed_iff (p : KleinPoint) :
    seamReflection p = p ↔ p.1 = 0 := by
  rcases p with ⟨ρ, θ⟩
  simp [seamReflection]
  constructor <;> intro h
  · linarith
  · rw [h]
    ring

theorem wallpaperGlide_square (L : ℝ) (p : KleinPoint) :
    wallpaperGlide L (wallpaperGlide L p) = (p.1, p.2 + L) := by
  rcases p with ⟨ρ, θ⟩
  simp [wallpaperGlide]
  ring

theorem wallpaperGlide_preserves_transverse_square (L : ℝ) (p : KleinPoint) :
    (wallpaperGlide L p).1 ^ 2 = p.1 ^ 2 := by
  simp [wallpaperGlide]

theorem evenMode_phase_shift (a : ℝ) (n : ℤ) (x : ℝ) (ha : a ≠ 0) :
    Complex.I * ((evenLongitudinalWaveNumber a n : ℂ) * (x + a / 2 : ℂ)) =
      Complex.I * ((evenLongitudinalWaveNumber a n : ℂ) * (x : ℂ)) +
        (n : ℂ) * (2 * Real.pi * Complex.I) := by
  unfold evenLongitudinalWaveNumber
  push_cast
  field_simp [ha]
  ring

theorem oddMode_phase_shift (a : ℝ) (n : ℤ) (x : ℝ) (ha : a ≠ 0) :
    Complex.I * ((oddLongitudinalWaveNumber a n : ℂ) * (x + a / 2 : ℂ)) =
      Complex.I * ((oddLongitudinalWaveNumber a n : ℂ) * (x : ℂ)) +
        (n : ℂ) * (2 * Real.pi * Complex.I) + Real.pi * Complex.I := by
  unfold oddLongitudinalWaveNumber
  push_cast
  field_simp [ha]
  ring

theorem evenMode_periodic_longitudinal (a b : ℝ) (n : ℤ) (m : ℕ)
    (x y : ℝ) (ha : a ≠ 0) :
    evenMode a b n m (longitudinalTranslation a (x, y)) =
      evenMode a b n m (x, y) := by
  simp only [evenMode, longitudinalTranslation]
  have hx :
      Complex.I * ((evenLongitudinalWaveNumber a n : ℂ) *
        ((x + a : ℝ) : ℂ)) =
        Complex.I * ((evenLongitudinalWaveNumber a n : ℂ) * (x : ℂ)) +
          (2 * n : ℂ) * (2 * Real.pi * Complex.I) := by
    unfold evenLongitudinalWaveNumber
    push_cast
    field_simp [ha]
    ring
  have hmult :
      (2 * (n : ℂ)) * (2 * Real.pi * Complex.I) =
        ((2 * n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [hx, Complex.exp_add, hmult, Complex.exp_int_mul_two_pi_mul_I]
  simp

theorem oddMode_periodic_longitudinal (a b : ℝ) (n : ℤ) (m : ℕ)
    (x y : ℝ) (ha : a ≠ 0) :
    oddMode a b n m (longitudinalTranslation a (x, y)) =
      oddMode a b n m (x, y) := by
  simp only [oddMode, longitudinalTranslation]
  have hx :
      Complex.I * ((oddLongitudinalWaveNumber a n : ℂ) *
        ((x + a : ℝ) : ℂ)) =
        Complex.I * ((oddLongitudinalWaveNumber a n : ℂ) * (x : ℂ)) +
          (2 * n + 1 : ℂ) * (2 * Real.pi * Complex.I) := by
    unfold oddLongitudinalWaveNumber
    push_cast
    field_simp [ha]
  have hmult :
      (2 * (n : ℂ) + 1) * (2 * Real.pi * Complex.I) =
        ((2 * n + 1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [hx, Complex.exp_add, hmult, Complex.exp_int_mul_two_pi_mul_I]
  simp

theorem evenMode_glide_invariant (a b : ℝ) (n : ℤ) (m : ℕ) (x y : ℝ)
    (ha : a ≠ 0) :
    evenMode a b n m (glide a (x, y)) = evenMode a b n m (x, y) := by
  simp only [evenMode, glide]
  have htrans :
      (transverseWaveNumber b m * -y : ℝ) =
        -(transverseWaveNumber b m * y) := by ring
  have htransC :
      ((transverseWaveNumber b m * -y : ℝ) : ℂ) =
        -((transverseWaveNumber b m * y : ℝ) : ℂ) := by
    simp [htrans]
  have hx : ((x + a / 2 : ℝ) : ℂ) = (x : ℂ) + (a : ℂ) / 2 := by
    push_cast
    rfl
  rw [htransC, Complex.cos_neg,
    hx, evenMode_phase_shift a n x ha, Complex.exp_add]
  rw [Complex.exp_int_mul_two_pi_mul_I]
  simp

theorem oddMode_glide_invariant (a b : ℝ) (n : ℤ) (m : ℕ) (x y : ℝ)
    (ha : a ≠ 0) :
    oddMode a b n m (glide a (x, y)) = oddMode a b n m (x, y) := by
  simp only [oddMode, glide]
  have htrans :
      (transverseWaveNumber b m * -y : ℝ) =
        -(transverseWaveNumber b m * y) := by ring
  have htransC :
      ((transverseWaveNumber b m * -y : ℝ) : ℂ) =
        -((transverseWaveNumber b m * y : ℝ) : ℂ) := by
    simp [htrans]
  have hx : ((x + a / 2 : ℝ) : ℂ) = (x : ℂ) + (a : ℂ) / 2 := by
    push_cast
    rfl
  rw [htransC, Complex.sin_neg,
    hx, oddMode_phase_shift a n x ha, Complex.exp_add]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    Complex.exp_pi_mul_I]
  simp

def kleinInvariant (a b : ℝ) (f : KleinPoint → ℂ) : Prop :=
  (∀ p, f (periodicTranslation b p) = f p) ∧
    (∀ p, f (glide a p) = f p)

theorem kleinInvariant_longitudinalTranslation
    (a b : ℝ) (f : KleinPoint → ℂ)
    (hf : kleinInvariant a b f) (p : KleinPoint) :
    f (longitudinalTranslation a p) = f p := by
  calc
    f (longitudinalTranslation a p) = f (glide a (glide a p)) := by
      rw [glide_square]
    _ = f (glide a p) := hf.2 _
    _ = f p := hf.2 _

theorem evenMode_kleinInvariant (a b : ℝ) (n : ℤ) (m : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    kleinInvariant a b (evenMode a b n m) := by
  constructor
  · intro p
    rcases p with ⟨x, y⟩
    exact evenMode_periodic_transverse a b n m x y hb
  · intro p
    rcases p with ⟨x, y⟩
    exact evenMode_glide_invariant a b n m x y ha

theorem oddMode_kleinInvariant (a b : ℝ) (n : ℤ) (m : ℕ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    kleinInvariant a b (oddMode a b n m) := by
  constructor
  · intro p
    rcases p with ⟨x, y⟩
    exact oddMode_periodic_transverse a b n m x y hb
  · intro p
    rcases p with ⟨x, y⟩
    exact oddMode_glide_invariant a b n m x y ha

theorem oddModePositive_glide_invariant (a b : ℝ) (n : ℤ)
    (m : PositiveTransverseIndex) (x y : ℝ) (ha : a ≠ 0) :
    oddModePositive a b n m (glide a (x, y)) =
      oddModePositive a b n m (x, y) := by
  exact oddMode_glide_invariant a b n m.1 x y ha

theorem oddModePositive_periodic_transverse (a b : ℝ) (n : ℤ)
    (m : PositiveTransverseIndex) (x y : ℝ) (hb : b ≠ 0) :
    oddModePositive a b n m (periodicTranslation b (x, y)) =
      oddModePositive a b n m (x, y) := by
  exact oddMode_periodic_transverse a b n m.1 x y hb

theorem oddModePositive_helmholtz (a b : ℝ) (n : ℤ)
    (m : PositiveTransverseIndex) (p : KleinPoint) :
    -flatLaplacian (oddModePositive a b n m) p =
      (oddBranchEigenvaluePositive a b n m : ℂ) *
        oddModePositive a b n m p := by
  exact oddMode_helmholtz a b n m.1 p

theorem oddModePositive_kleinInvariant (a b : ℝ) (n : ℤ)
    (m : PositiveTransverseIndex) (ha : a ≠ 0) (hb : b ≠ 0) :
    kleinInvariant a b (oddModePositive a b n m) := by
  constructor
  · intro p
    rcases p with ⟨x, y⟩
    exact oddModePositive_periodic_transverse a b n m x y hb
  · intro p
    rcases p with ⟨x, y⟩
    exact oddModePositive_glide_invariant a b n m x y ha

theorem oddModePositive_periodic_longitudinal (a b : ℝ) (n : ℤ)
    (m : PositiveTransverseIndex) (x y : ℝ) (ha : a ≠ 0) :
    oddModePositive a b n m (longitudinalTranslation a (x, y)) =
      oddModePositive a b n m (x, y) := by
  exact oddMode_periodic_longitudinal a b n m.1 x y ha

/-! ## Finite heat-trace readout

This is a finite spectral sum, not an assertion about the analytic heat trace
of a quotient manifold. -/

def evenHeatTrace (t a b : ℝ) (marks : Finset (ℤ × ℕ)) : ℝ :=
  ∑ q ∈ marks, Real.exp (-t * evenBranchEigenvalue a b q.1 q.2)

def oddHeatTrace (t a b : ℝ)
    (marks : Finset (ℤ × PositiveTransverseIndex)) : ℝ :=
  ∑ q ∈ marks, Real.exp (-t * oddBranchEigenvalue a b q.1 q.2.1)

def finiteKleinHeatTrace (t a b : ℝ)
    (evenMarks : Finset (ℤ × ℕ))
    (oddMarks : Finset (ℤ × PositiveTransverseIndex)) : ℝ :=
  evenHeatTrace t a b evenMarks + oddHeatTrace t a b oddMarks

def torusLongitudinalWaveNumber (a : ℝ) (n : ℤ) : ℝ :=
  2 * Real.pi * n / a

def torusEigenvalue (a b : ℝ) (n m : ℤ) : ℝ :=
  torusLongitudinalWaveNumber a n ^ 2 +
    torusLongitudinalWaveNumber b m ^ 2

/-- A finite readout of the ordinary torus Fourier lattice. -/
def finiteTorusHeatTrace (t a b : ℝ)
    (marks : Finset (ℤ × ℤ)) : ℝ :=
  ∑ q ∈ marks, Real.exp (-t * torusEigenvalue a b q.1 q.2)

def finiteCrosscapCorrection (t a b : ℝ)
    (evenMarks : Finset (ℤ × ℕ))
    (oddMarks : Finset (ℤ × PositiveTransverseIndex))
    (torusMarks : Finset (ℤ × ℤ)) : ℝ :=
  finiteKleinHeatTrace t a b evenMarks oddMarks -
    (1 / 2 : ℝ) * finiteTorusHeatTrace t a b torusMarks

theorem finiteKleinHeatTrace_eq_half_torus_add_crosscap
    (t a b : ℝ) (evenMarks : Finset (ℤ × ℕ))
    (oddMarks : Finset (ℤ × PositiveTransverseIndex))
    (torusMarks : Finset (ℤ × ℤ)) :
    finiteKleinHeatTrace t a b evenMarks oddMarks =
      (1 / 2 : ℝ) * finiteTorusHeatTrace t a b torusMarks +
        finiteCrosscapCorrection t a b evenMarks oddMarks torusMarks := by
  unfold finiteCrosscapCorrection
  ring

theorem evenHeatTrace_nonneg (t a b : ℝ) (marks : Finset (ℤ × ℕ)) :
    0 ≤ evenHeatTrace t a b marks := by
  unfold evenHeatTrace
  exact Finset.sum_nonneg fun q hq => Real.exp_nonneg _

theorem oddHeatTrace_nonneg (t a b : ℝ)
    (marks : Finset (ℤ × PositiveTransverseIndex)) :
    0 ≤ oddHeatTrace t a b marks := by
  unfold oddHeatTrace
  exact Finset.sum_nonneg fun q hq => Real.exp_nonneg _

theorem finiteKleinHeatTrace_nonneg (t a b : ℝ)
    (evenMarks : Finset (ℤ × ℕ))
    (oddMarks : Finset (ℤ × PositiveTransverseIndex)) :
    0 ≤ finiteKleinHeatTrace t a b evenMarks oddMarks := by
  exact add_nonneg (evenHeatTrace_nonneg t a b evenMarks)
    (oddHeatTrace_nonneg t a b oddMarks)

theorem finiteTorusHeatTrace_nonneg (t a b : ℝ)
    (marks : Finset (ℤ × ℤ)) :
    0 ≤ finiteTorusHeatTrace t a b marks := by
  unfold finiteTorusHeatTrace
  exact Finset.sum_nonneg fun q hq => Real.exp_nonneg _

theorem evenHeatTrace_zero (a b : ℝ) (marks : Finset (ℤ × ℕ)) :
    evenHeatTrace 0 a b marks = marks.card := by
  simp [evenHeatTrace]

theorem oddHeatTrace_zero (a b : ℝ)
    (marks : Finset (ℤ × PositiveTransverseIndex)) :
    oddHeatTrace 0 a b marks = marks.card := by
  simp [oddHeatTrace]

theorem finiteKleinHeatTrace_zero (a b : ℝ)
    (evenMarks : Finset (ℤ × ℕ))
    (oddMarks : Finset (ℤ × PositiveTransverseIndex)) :
    finiteKleinHeatTrace 0 a b evenMarks oddMarks =
      evenMarks.card + oddMarks.card := by
  simp [finiteKleinHeatTrace, evenHeatTrace_zero, oddHeatTrace_zero]

theorem finiteTorusHeatTrace_zero (a b : ℝ)
    (marks : Finset (ℤ × ℤ)) :
    finiteTorusHeatTrace 0 a b marks = marks.card := by
  simp [finiteTorusHeatTrace]

/-! ## Countable heat-trace readouts

The following definitions use Mathlib's `tsum` for the infinite Fourier
lattices.  They deliberately expose summability as a separate proposition:
the definitions alone do not assert convergence of a heat trace. -/

def evenHeatTerm (t a b : ℝ) (q : ℤ × ℕ) : ℝ :=
  Real.exp (-t * evenBranchEigenvalue a b q.1 q.2)

def oddHeatTerm (t a b : ℝ)
    (q : ℤ × PositiveTransverseIndex) : ℝ :=
  Real.exp (-t * oddBranchEigenvaluePositive a b q.1 q.2)

def torusHeatTerm (t a b : ℝ) (q : ℤ × ℤ) : ℝ :=
  Real.exp (-t * torusEigenvalue a b q.1 q.2)

def infiniteEvenHeatTrace (t a b : ℝ) : ℝ :=
  ∑' q : ℤ × ℕ, evenHeatTerm t a b q

def infiniteOddHeatTrace (t a b : ℝ) : ℝ :=
  ∑' q : ℤ × PositiveTransverseIndex, oddHeatTerm t a b q

def infiniteKleinHeatTrace (t a b : ℝ) : ℝ :=
  infiniteEvenHeatTrace t a b + infiniteOddHeatTrace t a b

def infiniteTorusHeatTrace (t a b : ℝ) : ℝ :=
  ∑' q : ℤ × ℤ, torusHeatTerm t a b q

def infiniteCrosscapCorrection (t a b : ℝ) : ℝ :=
  infiniteKleinHeatTrace t a b -
    (1 / 2 : ℝ) * infiniteTorusHeatTrace t a b

def InfiniteHeatTraceSummable (t a b : ℝ) : Prop :=
  Summable (evenHeatTerm t a b) ∧
    Summable (oddHeatTerm t a b) ∧
      Summable (torusHeatTerm t a b)

theorem summable_exp_neg_mul_sq_nat {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℕ => Real.exp (-r * (n : ℝ) ^ 2)) := by
  apply Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr hr) ?_
  intro n
  exact_mod_cast Nat.le_pow (by norm_num : 0 < 2)

theorem summable_exp_neg_mul_sq_int {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℤ => Real.exp (-r * (n : ℝ) ^ 2)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · exact Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr hr) (by
      intro n
      exact_mod_cast Nat.le_pow (by norm_num : 0 < 2))
  · simpa [Int.cast_neg, Int.cast_natCast, neg_sq] using
      (Real.summable_exp_nat_mul_of_ge (neg_lt_zero.mpr hr) (by
        intro n
        exact_mod_cast Nat.le_pow (by norm_num : 0 < 2)))

theorem summable_exp_neg_shifted_sq_int {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℤ =>
      Real.exp (-r * (2 * (n : ℝ) + 1) ^ 2)) := by
  have hbase := summable_exp_neg_mul_sq_int hr
  apply hbase.of_nonneg_of_le (fun n => Real.exp_nonneg _)
  intro n
  apply Real.exp_le_exp.mpr
  have hsq : (n : ℝ) ^ 2 ≤ (2 * (n : ℝ) + 1) ^ 2 := by
    by_cases hn : 0 ≤ n
    · have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [sq_nonneg (n : ℝ)]
    · have hn' : n ≤ -1 := by omega
      have hnR : (n : ℝ) ≤ -1 := by exact_mod_cast hn'
      have hp : 0 ≤ (3 * (-(n : ℝ)) - 1) * (-(n : ℝ) - 1) := by
        apply mul_nonneg <;> nlinarith
      nlinarith
  nlinarith

theorem summable_exp_neg_add_sq_int_nat {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    Summable (fun q : ℤ × ℕ =>
      Real.exp (-r * (q.1 : ℝ) ^ 2 - s * (q.2 : ℝ) ^ 2)) := by
  apply (summable_prod_of_nonneg (fun q => Real.exp_nonneg _)).2
  constructor
  · intro n
    have hm := summable_exp_neg_mul_sq_nat hs
    have hmul := hm.mul_left (Real.exp (-r * (n : ℝ) ^ 2))
    convert hmul using 1
    ext m
    rw [← Real.exp_add]
    congr 1
    ring
  · have hn := summable_exp_neg_mul_sq_int hr
    have hconst : Summable (fun n : ℤ =>
        Real.exp (-r * (n : ℝ) ^ 2) *
          (∑' m : ℕ, Real.exp (-s * (m : ℝ) ^ 2))) :=
      hn.mul_right _
    apply hconst.congr
    intro n
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    rw [← Real.exp_add]
    congr 1
    ring

theorem summable_exp_neg_add_sq_int_int {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    Summable (fun q : ℤ × ℤ =>
      Real.exp (-r * (q.1 : ℝ) ^ 2 - s * (q.2 : ℝ) ^ 2)) := by
  apply (summable_prod_of_nonneg (fun q => Real.exp_nonneg _)).2
  constructor
  · intro n
    have hm := summable_exp_neg_mul_sq_int hs
    have hmul := hm.mul_left (Real.exp (-r * (n : ℝ) ^ 2))
    convert hmul using 1
    ext m
    rw [← Real.exp_add]
    congr 1
    ring
  · have hn := summable_exp_neg_mul_sq_int hr
    have hconst : Summable (fun n : ℤ =>
        Real.exp (-r * (n : ℝ) ^ 2) *
          (∑' m : ℤ, Real.exp (-s * (m : ℝ) ^ 2))) :=
      hn.mul_right _
    apply hconst.congr
    intro n
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    rw [← Real.exp_add]
    congr 1
    ring

theorem summable_exp_neg_shifted_sq_int_posNat {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    Summable (fun q : ℤ × PositiveTransverseIndex =>
      Real.exp (-r * (2 * (q.1 : ℝ) + 1) ^ 2 -
        s * (q.2.1 : ℝ) ^ 2)) := by
  apply (summable_prod_of_nonneg (fun q => Real.exp_nonneg _)).2
  constructor
  · intro n
    have hm : Summable (fun m : PositiveTransverseIndex =>
        Real.exp (-s * (m.1 : ℝ) ^ 2)) := by
      simpa [Function.comp_def] using
        (summable_exp_neg_mul_sq_nat hs).subtype {m : ℕ | 0 < m}
    have hmul := hm.mul_left
      (Real.exp (-r * (2 * (n : ℝ) + 1) ^ 2))
    convert hmul using 1
    ext m
    rw [← Real.exp_add]
    congr 1
    ring
  · have hn := summable_exp_neg_shifted_sq_int hr
    have hconst : Summable (fun n : ℤ =>
        Real.exp (-r * (2 * (n : ℝ) + 1) ^ 2) *
          (∑' m : PositiveTransverseIndex,
            Real.exp (-s * (m.1 : ℝ) ^ 2))) :=
      hn.mul_right _
    apply hconst.congr
    intro n
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    rw [← Real.exp_add]
    congr 1
    ring

theorem summable_evenHeatTerm_of_pos
    {t a b : ℝ} (ht : 0 < t) (ha : a ≠ 0) (hb : b ≠ 0) :
    Summable (evenHeatTerm t a b) := by
  let r : ℝ := t * (4 * Real.pi / a) ^ 2
  let s : ℝ := t * (2 * Real.pi / b) ^ 2
  have hr : 0 < r := by
    dsimp [r]
    exact mul_pos ht (sq_pos_of_ne_zero (by
      intro h
      apply ha
      field_simp at h
      linarith [Real.pi_pos]))
  have hs : 0 < s := by
    dsimp [s]
    exact mul_pos ht (sq_pos_of_ne_zero (by
      intro h
      apply hb
      field_simp at h
      linarith [Real.pi_pos]))
  have h := summable_exp_neg_add_sq_int_nat hr hs
  apply h.congr
  intro q
  unfold evenHeatTerm evenBranchEigenvalue
  unfold evenLongitudinalWaveNumber transverseWaveNumber
  dsimp [r, s]
  congr 1
  ring

theorem summable_oddHeatTerm_of_pos
    {t a b : ℝ} (ht : 0 < t) (ha : a ≠ 0) (hb : b ≠ 0) :
    Summable (oddHeatTerm t a b) := by
  let r : ℝ := t * (2 * Real.pi / a) ^ 2
  let s : ℝ := t * (2 * Real.pi / b) ^ 2
  have hr : 0 < r := by
    dsimp [r]
    exact mul_pos ht (sq_pos_of_ne_zero (by
      intro h
      apply ha
      field_simp at h
      linarith [Real.pi_pos]))
  have hs : 0 < s := by
    dsimp [s]
    exact mul_pos ht (sq_pos_of_ne_zero (by
      intro h
      apply hb
      field_simp at h
      linarith [Real.pi_pos]))
  have h := summable_exp_neg_shifted_sq_int_posNat hr hs
  apply h.congr
  intro q
  unfold oddHeatTerm oddBranchEigenvaluePositive oddBranchEigenvalue
  unfold oddLongitudinalWaveNumber transverseWaveNumber
  dsimp [r, s]
  congr 1
  ring

theorem summable_torusHeatTerm_of_pos
    {t a b : ℝ} (ht : 0 < t) (ha : a ≠ 0) (hb : b ≠ 0) :
    Summable (torusHeatTerm t a b) := by
  let r : ℝ := t * (2 * Real.pi / a) ^ 2
  let s : ℝ := t * (2 * Real.pi / b) ^ 2
  have hr : 0 < r := by
    dsimp [r]
    exact mul_pos ht (sq_pos_of_ne_zero (by
      intro h
      apply ha
      field_simp at h
      linarith [Real.pi_pos]))
  have hs : 0 < s := by
    dsimp [s]
    exact mul_pos ht (sq_pos_of_ne_zero (by
      intro h
      apply hb
      field_simp at h
      linarith [Real.pi_pos]))
  have h := summable_exp_neg_add_sq_int_int hr hs
  apply h.congr
  intro q
  unfold torusHeatTerm torusEigenvalue torusLongitudinalWaveNumber
  dsimp [r, s]
  congr 1
  ring

theorem infiniteHeatTraceSummable_of_pos
    {t a b : ℝ} (ht : 0 < t) (ha : a ≠ 0) (hb : b ≠ 0) :
    InfiniteHeatTraceSummable t a b := by
  exact ⟨summable_evenHeatTerm_of_pos ht ha hb,
    summable_oddHeatTerm_of_pos ht ha hb,
    summable_torusHeatTerm_of_pos ht ha hb⟩

theorem infiniteKleinHeatTrace_eq_half_torus_add_crosscap
    (t a b : ℝ) :
    infiniteKleinHeatTrace t a b =
      (1 / 2 : ℝ) * infiniteTorusHeatTrace t a b +
        infiniteCrosscapCorrection t a b := by
  unfold infiniteCrosscapCorrection
  ring

theorem evenHeatTerm_nonneg (t a b : ℝ) (q : ℤ × ℕ) :
    0 ≤ evenHeatTerm t a b q := by
  exact Real.exp_nonneg _

theorem oddHeatTerm_nonneg (t a b : ℝ)
    (q : ℤ × PositiveTransverseIndex) :
    0 ≤ oddHeatTerm t a b q := by
  exact Real.exp_nonneg _

theorem torusHeatTerm_nonneg (t a b : ℝ) (q : ℤ × ℤ) :
    0 ≤ torusHeatTerm t a b q := by
  exact Real.exp_nonneg _

/-! ## Two-state chirality return under repeated glide circuits -/

inductive KleinChirality where
  | right
  | left
  deriving DecidableEq

def flipChirality : KleinChirality → KleinChirality
  | .right => .left
  | .left => .right

@[simp] theorem flipChirality_twice (c : KleinChirality) :
    flipChirality (flipChirality c) = c := by
  cases c <;> rfl

theorem flipChirality_fourth (c : KleinChirality) :
    flipChirality (flipChirality (flipChirality (flipChirality c))) = c := by
  rw [flipChirality_twice, flipChirality_twice]

theorem one_glide_flips_right :
    flipChirality .right = .left := rfl

theorem two_glides_restore_right :
    flipChirality (flipChirality .right) = .right := by
  simp

/-! ## The two permitted branches and the forbidden mixed branch -/

theorem evenBranch_has_even_glide_parity (n : ℤ) :
    glideInvariant evenTransverseParity (evenLongitudinalParity n) :=
  even_even_glideInvariant n

theorem oddBranch_has_odd_glide_parity (n : ℤ) :
    glideInvariant oddTransverseParity (oddLongitudinalParity n) :=
  odd_odd_glideInvariant n

theorem mixed_odd_transverse_even_longitudinal_impossible (n : ℤ) :
    ¬ glideInvariant oddTransverseParity (evenLongitudinalParity n) :=
  odd_even_glide_forbidden n

/-! ## Basic algebraic branch readouts -/

theorem evenBranch_longitudinal_step (a : ℝ) (n : ℤ) :
    evenLongitudinalWaveNumber a n =
      2 * (2 * Real.pi * n / a) := by
  unfold evenLongitudinalWaveNumber
  ring

theorem kleinBottle_finite_spectrum_synthesis
    (a b t : ℝ) (n : ℤ) (m : ℕ) (x y : ℝ)
    (ha : a ≠ 0) (evenMarks : Finset (ℤ × ℕ))
    (oddMarks : Finset (ℤ × PositiveTransverseIndex)) :
    0 ≤ evenBranchEigenvalue a b n m ∧
    0 ≤ oddBranchEigenvalue a b n m ∧
    evenMode a b n m (glide a (x, y)) = evenMode a b n m (x, y) ∧
    oddMode a b n m (glide a (x, y)) = oddMode a b n m (x, y) ∧
    0 ≤ finiteKleinHeatTrace t a b evenMarks oddMarks := by
  exact ⟨evenBranchEigenvalue_nonneg a b n m,
    oddBranchEigenvalue_nonneg a b n m,
    evenMode_glide_invariant a b n m x y ha,
    oddMode_glide_invariant a b n m x y ha,
    finiteKleinHeatTrace_nonneg t a b evenMarks oddMarks⟩

end InfoGeometry.Physics.KleinBottleSpectrum

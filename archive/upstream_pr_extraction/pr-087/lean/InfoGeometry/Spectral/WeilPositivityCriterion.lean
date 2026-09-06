import Mathlib.Tactic
import InfoGeometry.Spectral.WeilPositivityGNSBridge

/-!
# Finite Weil positivity criterion

This owner separates finite positivity theorems from the global arithmetic
criterion. The former are native finite-sum statements. The latter requires
an arithmetic test-function carrier, convolution, involution, and zero data;
it is therefore kept separate from the finite Euclidean statements below.
-/

noncomputable section

namespace InfoGeometry.Spectral.WeilPositivityCriterion

open InfoGeometry.Spectral.WeilPositivity

/-! ## Finite prime-power comb -/

structure PrimePowerEntry where
  prime : ℕ
  power : ℕ
  logPrime : ℝ
  weight : ℝ

def primePowerTerm (p : PrimePowerEntry) (f : ℝ → ℝ) : ℝ :=
  p.weight * (f (p.power * p.logPrime) + f (-(p.power * p.logPrime)))

def weilArithmeticComb (entries : List PrimePowerEntry) (f : ℝ → ℝ) : ℝ :=
  (entries.map (fun p => primePowerTerm p f)).sum

theorem weilArithmeticComb_eq_sum (entries : List PrimePowerEntry) (f : ℝ → ℝ) :
    weilArithmeticComb entries f =
      (entries.map (fun p => primePowerTerm p f)).sum :=
  rfl

theorem weilArithmeticComb_add
    (entries : List PrimePowerEntry) (f g : ℝ → ℝ) :
    weilArithmeticComb entries (fun x => f x + g x) =
      weilArithmeticComb entries f + weilArithmeticComb entries g := by
  induction entries with
  | nil => simp [weilArithmeticComb]
  | cons p entries ih =>
      change primePowerTerm p (fun x => f x + g x) +
          weilArithmeticComb entries (fun x => f x + g x) =
        (primePowerTerm p f + weilArithmeticComb entries f) +
          (primePowerTerm p g + weilArithmeticComb entries g)
      rw [ih]
      unfold primePowerTerm
      ring

theorem weilArithmeticComb_smul
    (entries : List PrimePowerEntry) (c : ℝ) (f : ℝ → ℝ) :
    weilArithmeticComb entries (fun x => c * f x) =
      c * weilArithmeticComb entries f := by
  induction entries with
  | nil => simp [weilArithmeticComb]
  | cons p entries ih =>
      change primePowerTerm p (fun x => c * f x) +
          weilArithmeticComb entries (fun x => c * f x) =
        c * (primePowerTerm p f + weilArithmeticComb entries f)
      rw [ih]
      unfold primePowerTerm
      ring

theorem weilArithmeticComb_nonneg_of_termwise
    (entries : List PrimePowerEntry) (f : ℝ → ℝ)
    (hterm : ∀ p ∈ entries, 0 ≤ primePowerTerm p f) :
    0 ≤ weilArithmeticComb entries f := by
  induction entries with
  | nil =>
      simp [weilArithmeticComb]
  | cons p entries ih =>
      have hp : 0 ≤ primePowerTerm p f := hterm p (by simp)
      have hrest : ∀ q ∈ entries, 0 ≤ primePowerTerm q f := by
        intro q hq
        exact hterm q (by simp [hq])
      simpa [weilArithmeticComb] using add_nonneg hp (ih hrest)

theorem primePowerTerm_nonneg_of_nonneg
    (p : PrimePowerEntry) (f : ℝ → ℝ)
    (hw : 0 ≤ p.weight)
    (hf₁ : 0 ≤ f (p.power * p.logPrime))
    (hf₂ : 0 ≤ f (-(p.power * p.logPrime))) :
    0 ≤ primePowerTerm p f := by
  unfold primePowerTerm
  exact mul_nonneg hw (add_nonneg hf₁ hf₂)

theorem weilArithmeticComb_nonneg_of_nonneg
    (entries : List PrimePowerEntry) (f : ℝ → ℝ)
    (hweight : ∀ p ∈ entries, 0 ≤ p.weight)
    (hvalue₁ : ∀ p ∈ entries, 0 ≤ f (p.power * p.logPrime))
    (hvalue₂ : ∀ p ∈ entries, 0 ≤ f (-(p.power * p.logPrime))) :
    0 ≤ weilArithmeticComb entries f := by
  apply weilArithmeticComb_nonneg_of_termwise
  intro p hp
  exact primePowerTerm_nonneg_of_nonneg p f
    (hweight p hp) (hvalue₁ p hp) (hvalue₂ p hp)

/-! ## Finite spectral positivity -/

theorem finite_weil_pairing_nonneg (waves : Finset ModalWavepacket) :
    0 ≤ finiteSpectralPairing waves :=
  finiteSpectralPairing_nonneg waves

theorem finite_weil_pairing_zero_iff (waves : Finset ModalWavepacket) :
    finiteSpectralPairing waves = 0 ↔
      ∀ g ∈ waves, g.re = 0 ∧ g.im = 0 :=
  finiteSpectralPairing_eq_zero_iff waves

theorem weilArithmeticComb_zero (entries : List PrimePowerEntry) :
    weilArithmeticComb entries (fun _ => 0) = 0 := by
  induction entries with
  | nil => rfl
  | cons p entries ih =>
      simp [weilArithmeticComb, primePowerTerm, ih]

end InfoGeometry.Spectral.WeilPositivityCriterion

end noncomputable section

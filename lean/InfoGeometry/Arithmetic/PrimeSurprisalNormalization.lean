import Mathlib
import InfoGeometry.Basic
import InfoGeometry.Thermodynamics.SouriauTemperature
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Arithmetic.PrimeSurprisalNormalization

Finite normalization and surprisal identities for the prime-weight geometry.

This module proves the clean theorem-safe bridge:

* normalized weights produce surprisal `-log p + log Z`;
* finite prime products turn multiplicative weights into additive log energies;
* the same identities extend to complex Souriau temperatures by taking the
  real-part temperature readout.

The analytic identification with `ζ` remains separate.
-/

noncomputable section

open scoped BigOperators

namespace PrimeSurprisalNormalization

open InfoGeometry.Thermodynamics

/-! ## 1. Normalized weights and surprisal -/

/-- Normalized weight `p_i / Z`. -/
def normalizedWeight {α : Type*} (w : α → ℝ) (Z : ℝ) (a : α) : ℝ :=
  w a / Z

lemma normalizedWeight_nonneg {α : Type*} {w : α → ℝ} {Z : ℝ}
    (hZ : 0 ≤ Z) (hw : ∀ a, 0 ≤ w a) (a : α) :
    0 ≤ normalizedWeight w Z a := by
  unfold normalizedWeight
  exact div_nonneg (hw a) hZ

lemma normalizedWeight_pos {α : Type*} {w : α → ℝ} {Z : ℝ}
    (hZ : 0 < Z) {a : α} (hw : 0 < w a) :
    0 < normalizedWeight w Z a := by
  unfold normalizedWeight
  exact div_pos hw hZ

/-- Surprisal associated to a normalized weight. -/
def normalizedSurprisal {α : Type*} (w : α → ℝ) (Z : ℝ) (a : α) : ℝ :=
  -Real.log (normalizedWeight w Z a)

/--
Normalized surprisal is the affine log transform

`-log (w_i / Z) = -log w_i + log Z`.
-/
theorem normalizedSurprisal_eq_neg_log_weight_add_logZ
    {α : Type*} (w : α → ℝ) (Z : ℝ) (a : α)
    (hw : 0 < w a) (hZ : 0 < Z) :
    normalizedSurprisal w Z a = -Real.log (w a) + Real.log Z := by
  unfold normalizedSurprisal normalizedWeight
  rw [Real.log_div hw.ne' hZ.ne']
  ring

/--
Specialization where the normalizer is the finite partition
`Z = ∑ a, w a`.
-/
theorem normalizedSurprisal_eq_neg_log_weight_add_log_partition
    {α : Type*} [Fintype α] (w : α → ℝ) (a : α)
    (hw : 0 < w a) (hZ : 0 < ∑ x, w x) :
    normalizedSurprisal w (∑ x, w x) a =
      -Real.log (w a) + Real.log (∑ x, w x) := by
  exact normalizedSurprisal_eq_neg_log_weight_add_logZ w (∑ x, w x) a hw hZ

/-! ## 2. Prime-product surprisal -/

/-- Multiplicative finite weight on a finite prime-support set. -/
def primeProductWeight (q : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  S.prod q

lemma primeProductWeight_pos {q : ℕ → ℝ} {S : Finset ℕ}
    (hq : ∀ p ∈ S, 0 < q p) :
    0 < primeProductWeight q S := by
  unfold primeProductWeight
  exact Finset.prod_pos hq

lemma primeProductWeight_ne_zero {q : ℕ → ℝ} {S : Finset ℕ}
    (hq : ∀ p ∈ S, q p ≠ 0) :
    primeProductWeight q S ≠ 0 := by
  unfold primeProductWeight
  exact Finset.prod_ne_zero_iff.mpr hq

/-- Surprisal of a finite prime-product weight. -/
def primeProductSurprisal (q : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  -Real.log (primeProductWeight q S)

/--
Finite prime product turns into an additive sum of log-weights:

`-log (∏ q_p) = ∑ -log q_p`.
-/
theorem primeProductSurprisal_eq_sum
    (q : ℕ → ℝ) (S : Finset ℕ)
    (hq : ∀ p ∈ S, 0 < q p) :
    primeProductSurprisal q S = S.sum (fun p => -Real.log (q p)) := by
  unfold primeProductSurprisal primeProductWeight
  rw [Real.log_prod (by
    intro p hp
    exact (hq p hp).ne')]
  simp [Finset.sum_neg_distrib]

/--
Prime occupation with the Souriau kernel `q_p = exp(-s log p)` at real
temperature `s`.
-/
def primeSouriauWeight (s : ℝ) (p : ℕ) : ℝ :=
  Real.exp (-s * Real.log p)

lemma primeSouriauWeight_pos (s : ℝ) (p : ℕ) :
    0 < primeSouriauWeight s p := by
  unfold primeSouriauWeight
  exact Real.exp_pos _

/--
For a real Souriau temperature, the finite prime-product surprisal is the
linear energy `s ∑ log p`.
-/
theorem primeSouriauWeight_surprisal_eq_mul_log
    (s : ℝ) (p : ℕ) :
    -Real.log (primeSouriauWeight s p) = s * Real.log p := by
  unfold primeSouriauWeight
  rw [Real.log_exp]
  ring

/--
The finite prime-product surprisal at real Souriau temperature is the
weighted log-volume:

`-log (∏ exp(-s log p)) = s * ∑ log p`.
-/
theorem primeSouriauProductSurprisal_eq_mul_sum
    (s : ℝ) (S : Finset ℕ) :
    -Real.log (S.prod (primeSouriauWeight s)) =
      s * S.sum (fun p => Real.log p) := by
  unfold primeSouriauWeight
  have hlog :
      Real.log (S.prod (fun p => Real.exp (-s * Real.log p)))
        = S.sum (fun p => (-s * Real.log p)) := by
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl ?_
      intro p hp
      simp
    · intro p hp
      positivity
  rw [hlog]
  rw [← Finset.mul_sum]
  ring

/-! ## 3. Complex Souriau temperature projection -/

/--
Complex Souriau temperature projected to a real-part Gibbs weight.

This is the theorem-safe extension of the real normalization law to the
complex temperature axis: only the real part contributes to the positive
weight.
-/
def complexPrimeSouriauWeight (s : ℂ) (p : ℕ) : ℝ :=
  Real.exp (-(s.re) * Real.log p)

lemma complexPrimeSouriauWeight_pos (s : ℂ) (p : ℕ) :
    0 < complexPrimeSouriauWeight s p := by
  unfold complexPrimeSouriauWeight
  exact Real.exp_pos _

/--
Complex Souriau temperature specialization of the prime surprisal law.

The complex parameter enters only through its real part, which is the
thermodynamically meaningful inverse-temperature coordinate.
-/
theorem complexPrimeSouriauWeight_surprisal_eq_re_mul_log
    (s : ℂ) (p : ℕ) :
    -Real.log (complexPrimeSouriauWeight s p) = s.re * Real.log p := by
  unfold complexPrimeSouriauWeight
  rw [Real.log_exp]
  ring

/--
Finite prime-product surprisal at complex Souriau temperature, projected to the
real-part Gibbs weight.
-/
theorem complexPrimeSouriauProductSurprisal_eq_re_mul_sum
    (s : ℂ) (S : Finset ℕ) :
    -Real.log (S.prod (complexPrimeSouriauWeight s)) =
      s.re * S.sum (fun p => Real.log p) := by
  unfold complexPrimeSouriauWeight
  have hlog :
      Real.log (S.prod (fun p => Real.exp (-(s.re) * Real.log p)))
        = S.sum (fun p => (-(s.re) * Real.log p)) := by
    rw [Real.log_prod]
    · refine Finset.sum_congr rfl ?_
      intro p hp
      simp
    · intro p hp
      positivity
  rw [hlog]
  rw [← Finset.mul_sum]
  ring

/-! ## 4. Prime-register owner target -/

end PrimeSurprisalNormalization

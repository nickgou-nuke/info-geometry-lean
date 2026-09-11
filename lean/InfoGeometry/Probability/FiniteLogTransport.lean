import InfoGeometry.Probability.AitchisonFinite
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Probability.FiniteMedianShift
import Mathlib

/-!
# Ensemble-centered transport of finite positive spectral rows

Distances are columns; energies supply independent rows of positive restored
observations. Centering uses every distance, never a selected reference.
The exact collapse theorem assumes separability; the general identities retain
residuals. Robust estimation is the native global minimum of absolute loss.
No sampling precision or physical time interpretation is asserted.
Finite algebra checks: `scripts/verify_finite_log_transport.py`.
-/

noncomputable section
open scoped BigOperators
namespace InfoGeometry.Probability.FiniteLogTransport

open AitchisonFinite

def mean {m : ℕ} (x : Fin m → ℝ) : ℝ := (∑ j, x j) / m

def center {m : ℕ} (x : Fin m → ℝ) (j : Fin m) : ℝ := x j - mean x

theorem sum_center {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) :
    ∑ j, center x j = 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [center, mean, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem center_add {m : ℕ} (x y : Fin m → ℝ) (j : Fin m) :
    center (fun k => x k + y k) j = center x j + center y j := by
  simp only [center, mean, Finset.sum_add_distrib, add_div]
  ring

theorem center_const_add {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) (c : ℝ)
    (j : Fin m) : center (fun k => c + x k) j = center x j := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [center, mean, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, add_div]
  field_simp
  ring

theorem center_idempotent {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) :
    center (center x) = center x := by
  funext j
  change center x j - (∑ k, center x k) / m = center x j
  rw [sum_center hm x]
  simp

theorem product_centered_scales {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) :
    ∏ j, Real.exp (center x j) = 1 := by
  rw [← Real.exp_sum, sum_center hm x, Real.exp_zero]

/-- Among uniform translations, precisely one has zero sum. -/
theorem unique_centering_constant {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) (c : ℝ) :
    (∑ j, (x j - c)) = 0 ↔ c = mean x := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [mean, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  constructor
  · intro h
    apply (eq_div_iff hm0).mpr
    nlinarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Identification with the existing finite simplex CLR owner. -/
theorem center_eq_clr {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) :
    clr (softmax m (center x) hm) hm = center x := by
  funext j
  exact clr_softmax_centered (center x) hm (sum_center hm x) j

def logRow {m : ℕ} (L : Fin m → ℝ) : Fin m → ℝ := fun j => Real.log (L j)

/-- Multiplication by a positive row constant cancels exactly after centering. -/
theorem logRow_channel_cancel {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ)
    (hg : ∀ j, 0 < g j) (a : ℝ) (ha : 0 < a) :
    center (logRow (fun j => a * g j)) = center (logRow g) := by
  funext j
  have hrow : logRow (fun k => a * g k) = fun k => Real.log a + Real.log (g k) := by
    funext k
    exact Real.log_mul ha.ne' (hg k).ne'
  rw [hrow]
  exact center_const_add hm _ _ j

/-- Arbitrary per-spectrum scale changes act by centered additive shifts. -/
theorem logRow_gauge {m : ℕ} (L : Fin m → ℝ) (hL : ∀ j, 0 < L j)
    (w : Fin m → ℝ) (j : Fin m) :
    center (logRow (fun k => L k * Real.exp (w k))) j =
      center (logRow L) j + center w j := by
  have hrow : logRow (fun k => L k * Real.exp (w k)) =
      fun k => logRow L k + w k := by
    funext k
    simp [logRow, Real.log_mul (hL k).ne' (Real.exp_ne_zero _)]
  rw [hrow]
  exact center_add _ _ _

def transport {m : ℕ} (L s : Fin m → ℝ) (j : Fin m) : ℝ :=
  L j * Real.exp (-center s j)

theorem log_transport {m : ℕ} (L s : Fin m → ℝ) (hL : ∀ j, 0 < L j)
    (j : Fin m) : Real.log (transport L s j) = logRow L j - center s j := by
  simp [transport, logRow, Real.log_mul (hL j).ne' (Real.exp_ne_zero _)]
  ring

/-- The transported log row retains exactly the estimated shift residual. -/
theorem transport_residual {m : ℕ} (L s : Fin m → ℝ) (hL : ∀ j, 0 < L j)
    (j : Fin m) :
    Real.log (transport L s j) - mean (logRow L) =
      center (logRow L) j - center s j := by
  rw [log_transport L s hL j]
  simp only [center]
  ring

theorem separable_transport {m : ℕ} (g : Fin m → ℝ)
    (hg : ∀ j, 0 < g j) (a : ℝ) (ha : 0 < a) (j : Fin m) :
    transport (fun k => a * g k) (logRow g) j =
      a * Real.exp (mean (logRow g)) := by
  have hlog := log_transport (fun k => a * g k) (logRow g)
    (fun k => mul_pos ha (hg k)) j
  have heq : Real.log (transport (fun k => a * g k) (logRow g) j) =
      Real.log a + mean (logRow g) := by
    rw [hlog]
    simp [logRow, center, Real.log_mul ha.ne' (hg j).ne']
    ring
  have ht : 0 < transport (fun k => a * g k) (logRow g) j := by
    exact mul_pos (mul_pos ha (hg j)) (Real.exp_pos _)
  have hexp := congrArg Real.exp heq
  simpa [Real.exp_log ht, Real.exp_add, Real.exp_log ha] using hexp

/-- Per-spectrum median deviations, with the per-energy mean-log baseline fixed. -/
def spectrumShift {n m : ℕ} (L : Fin n → Fin m → ℝ) (j : Fin m) : ℝ :=
  FiniteMedianShift.median (fun i => center (logRow (L i)) j)

/-- Collective transport with no chosen reference distance. -/
def robustTransport {n m : ℕ} (L : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  transport (L i) (spectrumShift L) j

/-- Exact recovery of the common centered scale for any finite separable matrix. -/
theorem spectrumShift_separable {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (a : Fin n → ℝ) (g : Fin m → ℝ) (ha : ∀ i, 0 < a i) (hg : ∀ j, 0 < g j) :
    spectrumShift (fun i j => a i * g j) = center (logRow g) := by
  funext j
  unfold spectrumShift
  have hrow : (fun i => center (logRow (fun k => a i * g k)) j) =
      fun _ : Fin n => center (logRow g) j := by
    funext i
    rw [logRow_channel_cancel hm g hg (a i) (ha i)]
  rw [hrow]
  exact FiniteMedianShift.median_constant hn _

/-- The median estimator, not a supplied true scale, achieves exact model collapse. -/
theorem robustTransport_separable {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (a : Fin n → ℝ) (g : Fin m → ℝ) (ha : ∀ i, 0 < a i) (hg : ∀ j, 0 < g j)
    (i : Fin n) (j : Fin m) :
    robustTransport (fun k t => a k * g t) i j =
      a i * Real.exp (mean (logRow g)) := by
  unfold robustTransport
  rw [spectrumShift_separable hn hm a g ha hg]
  unfold transport
  rw [center_idempotent hm]
  exact separable_transport g hg (a i) (ha i) j

/-- The applied column estimator inherits the sharp finite majority bound. -/
theorem spectrumShift_robust {n m : ℕ} (L : Fin n → Fin m → ℝ)
    (j : Fin m) (θ δ : ℝ) (good : Finset (Fin n))
    (hmajority : goodᶜ.card < good.card)
    (hgood : ∀ i ∈ good, |center (logRow (L i)) j - θ| ≤ δ) :
    |spectrumShift L j - θ| ≤ δ := by
  exact FiniteMedianShift.median_interval _ _ θ δ
    (FiniteMedianShift.median_minimizes _) good hmajority hgood

/-- Gauge fixing can at most double a uniform shift-error bound. -/
theorem center_error_bound {m : ℕ} (hm : 0 < m) (s t : Fin m → ℝ) (δ : ℝ)
    (h : ∀ j, |s j - t j| ≤ δ) (j : Fin m) :
    |center s j - center t j| ≤ 2 * δ := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => h k)
  have habs := Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun k => s k - t k)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have havg : |mean s - mean t| ≤ δ := by
    have heq : mean s - mean t = (∑ k, (s k - t k)) / m := by
      simp [mean, Finset.sum_sub_distrib, sub_div]
    rw [heq, abs_div, abs_of_pos hmR]
    apply (div_le_iff₀ hmR).mpr
    nlinarith
  have ht := abs_sub (s j - t j) (mean s - mean t)
  have heq : center s j - center t j = (s j - t j) - (mean s - mean t) := by
    unfold center
    ring
  rw [heq]
  linarith [h j]

end InfoGeometry.Probability.FiniteLogTransport

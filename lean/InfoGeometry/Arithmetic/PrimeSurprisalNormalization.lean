import Mathlib
import InfoGeometry.Basic
import InfoGeometry.Thermodynamics.SouriauTemperature
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Meta.BridgeTarget

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

namespace InfoGeometry.Arithmetic.PrimeSurprisalNormalization

open InfoGeometry.Thermodynamics

/-! ## 1. Normalized weights and surprisal -/

/-- Normalized weight `p_i / Z`. -/
def normalizedWeight {α : Type*} (w : α → ℝ) (Z : ℝ) (a : α) : ℝ :=
  w a / Z

/-- Surprisal associated to a normalized weight. -/
def normalizedSurprisal {α : Type*} (w : α → ℝ) (Z : ℝ) (a : α) : ℝ :=
  -Real.log (normalizedWeight w Z a)

/--
Normalized surprisal is the affine log transform

`-log (w_i / Z) = -log w_i + log Z`.
-/
@[bridge_target_tag, rep_depth thermo]
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
@[bridge_target_tag, rep_depth thermo]
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

/-- Surprisal of a finite prime-product weight. -/
def primeProductSurprisal (q : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  -Real.log (primeProductWeight q S)

/--
Finite prime product turns into an additive sum of log-weights:

`-log (∏ q_p) = ∑ -log q_p`.
-/
@[bridge_target_tag, rep_depth thermo]
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

/--
For a real Souriau temperature, the finite prime-product surprisal is the
linear energy `s ∑ log p`.
-/
@[bridge_target_tag, rep_depth thermo]
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
@[bridge_target_tag, rep_depth thermo]
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

/--
Complex Souriau temperature specialization of the prime surprisal law.

The complex parameter enters only through its real part, which is the
thermodynamically meaningful inverse-temperature coordinate.
-/
@[bridge_target_tag, rep_depth thermo]
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
@[bridge_target_tag, rep_depth thermo]
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

/--
Owner target for the finite surprisal normalization bridge.

This closes:
* normalization as affine surprisal shift;
* finite prime product as additive log energy;
* real-part complex Souriau extension.
-/
@[owner_target_tag]
def PrimeSurprisalNormalizationOwnerTarget : Prop :=
  (∀ {α : Type*} (w : α → ℝ) (Z : ℝ) (a : α),
      0 < w a → 0 < Z →
      normalizedSurprisal w Z a = -Real.log (w a) + Real.log Z)
  ∧
  (∀ (q : ℕ → ℝ) (S : Finset ℕ),
      (∀ p ∈ S, 0 < q p) →
      primeProductSurprisal q S = S.sum (fun p => -Real.log (q p)))
  ∧
  (∀ (s : ℂ) (S : Finset ℕ),
      -Real.log (S.prod (complexPrimeSouriauWeight s)) =
        s.re * S.sum (fun p => Real.log p))

/-- The finite surprisal normalization owner target is proved. -/
theorem primeSurprisalNormalizationOwnerTarget :
    PrimeSurprisalNormalizationOwnerTarget := by
  refine ⟨?_, ?_, ?_⟩
  · intro α w Z a hw hZ
    exact normalizedSurprisal_eq_neg_log_weight_add_logZ w Z a hw hZ
  · intro q S hq
    exact primeProductSurprisal_eq_sum q S hq
  · intro s S
    exact complexPrimeSouriauProductSurprisal_eq_re_mul_sum s S

end InfoGeometry.Arithmetic.PrimeSurprisalNormalization

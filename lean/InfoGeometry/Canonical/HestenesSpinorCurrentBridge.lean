/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HestenesSTA4DMaxwellDiracBridge
import InfoGeometry.Canonical.HestenesNativeDiracCurrent
import InfoGeometry.Canonical.HestenesNativeSpinorFrame
import InfoGeometry.Canonical.HestenesCurrentReadout
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# From the eight real spinor coefficients to the native Clifford current

The existing `STASpinor.current_j0` is a polynomial in eight real fields.
This owner connects those fields to the actual even Clifford algebra by the
ordered frame `[1, γ₀γ₁, γ₀γ₂, γ₀γ₃, γ₂γ₃, γ₃γ₁, γ₁γ₂, γ₀γ₁γ₂γ₃]`.
The resulting native `diracCurrent` is the image of the explicit real vector
`currentVector`; its calibrated scalar time readout is exactly the existing
eight-square polynomial.

Definiteness of that polynomial proves injectivity of the coefficient
synthesis map and of the record encoder. Every encoded spinor has a genuine
vector current, and a nonzero encoded spinor has a nonzero current with
strictly positive time component. No normalization, invertibility, Fierz
identity, or field equation is assumed. Surjectivity onto the full even
algebra and current conservation are not asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesSpinorCurrentBridge

open HestenesCl14
open InfoGeometry.Canonical.SpacetimeAlgebra
open InfoGeometry.Canonical.HestenesNativeDiracCurrent
open InfoGeometry.Canonical.HestenesNativeSpinorFrame
open InfoGeometry.Canonical.HestenesCurrentReadout
open scoped BigOperators

/-- The existing record and its eight ordered real coordinates are equivalent.
The order retains the `γ₃γ₁` blade attached to `b31`. -/
def coefficients : STASpinor ≃ (Fin 8 → ℝ) where
  toFun ψ := fun
    | 0 => ψ.s0
    | 1 => ψ.b01
    | 2 => ψ.b02
    | 3 => ψ.b03
    | 4 => ψ.b23
    | 5 => ψ.b31
    | 6 => ψ.b12
    | 7 => ψ.p
  invFun c := ⟨c 0, c 1, c 2, c 3, c 4, c 5, c 6, c 7⟩
  left_inv ψ := by cases ψ; rfl
  right_inv c := by
    funext i
    fin_cases i <;> rfl

/-- The existing record has no zero instance; this is its zero coefficient tuple. -/
def zeroSpinor : STASpinor := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

@[simp] theorem coefficients_zero : coefficients zeroSpinor = 0 := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem coefficients_symm_zero : coefficients.symm 0 = zeroSpinor := rfl

theorem coefficients_eq_zero_iff (ψ : STASpinor) :
    coefficients ψ = 0 ↔ ψ = zeroSpinor := by
  constructor
  · intro h
    exact coefficients.injective (h.trans coefficients_zero.symm)
  · rintro rfl
    exact coefficients_zero

/-- The finite sum of squared coordinates is the already owned density polynomial. -/
theorem sum_sq_coefficients (ψ : STASpinor) :
    (∑ i : Fin 8, coefficients ψ i ^ 2) = STASpinor.current_j0 ψ := by
  simp [coefficients, STASpinor.current_j0, Fin.sum_univ_succ] <;> ring

/-- The frame's literal Clifford sandwich is the already owned native current. -/
theorem diracCurrent_synthesis_eq_iota (c : Fin 8 → ℝ) :
    diracCurrent (synthesis c) = ι14 (currentVector c) :=
  synthesis_sandwich_eq_iota c

/-- The actual native current has the positive coefficient quadratic form as its
calibrated time component. -/
theorem timeCoefficient_diracCurrent_synthesis (c : Fin 8 → ℝ) :
    timeCoefficient (diracCurrent (synthesis c)) = ∑ i : Fin 8, c i ^ 2 := by
  rw [diracCurrent_synthesis_eq_iota, timeCoefficient_iota, currentVector_time]

theorem sum_sq_eq_zero_iff (c : Fin 8 → ℝ) :
    (∑ i : Fin 8, c i ^ 2) = 0 ↔ c = 0 := by
  constructor
  · intro h
    have hc := (Finset.sum_sq_eq_zero_iff (Finset.univ : Finset (Fin 8)) c).mp h
    funext i
    exact hc i (Finset.mem_univ i)
  · rintro rfl
    simp

theorem timeCoefficient_diracCurrent_synthesis_nonneg (c : Fin 8 → ℝ) :
    0 ≤ timeCoefficient (diracCurrent (synthesis c)) := by
  rw [timeCoefficient_diracCurrent_synthesis]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (c i))

theorem timeCoefficient_diracCurrent_synthesis_eq_zero_iff (c : Fin 8 → ℝ) :
    timeCoefficient (diracCurrent (synthesis c)) = 0 ↔ c = 0 := by
  rw [timeCoefficient_diracCurrent_synthesis, sum_sq_eq_zero_iff]

/-- A zero native even element has zero current; positivity then recovers all
eight coefficients. Linear subtraction upgrades that fact to injectivity. -/
theorem synthesis_injective : Function.Injective synthesis := by
  intro c d hcd
  have hs : synthesis (c - d) = 0 := by
    rw [map_sub, hcd, sub_self]
  have ht : timeCoefficient (diracCurrent (synthesis (c - d))) = 0 := by
    simp [hs, diracCurrent]
  exact sub_eq_zero.mp ((timeCoefficient_diracCurrent_synthesis_eq_zero_iff (c - d)).mp ht)

theorem synthesis_eq_zero_iff (c : Fin 8 → ℝ) : synthesis c = 0 ↔ c = 0 := by
  constructor
  · intro h
    apply synthesis_injective
    simpa using h
  · rintro rfl
    exact map_zero synthesis

/-- Vanishing of the full Clifford current is equivalent to zero coefficients. -/
theorem diracCurrent_synthesis_eq_zero_iff (c : Fin 8 → ℝ) :
    diracCurrent (synthesis c) = 0 ↔ c = 0 := by
  constructor
  · intro h
    apply (timeCoefficient_diracCurrent_synthesis_eq_zero_iff c).mp
    simp only [h, map_zero]
  · rintro rfl
    simp [diracCurrent]

theorem diracCurrent_synthesis_ne_zero {c : Fin 8 → ℝ} (hc : c ≠ 0) :
    diracCurrent (synthesis c) ≠ 0 :=
  fun h => hc ((diracCurrent_synthesis_eq_zero_iff c).mp h)

theorem timeCoefficient_diracCurrent_synthesis_pos {c : Fin 8 → ℝ} (hc : c ≠ 0) :
    0 < timeCoefficient (diracCurrent (synthesis c)) := by
  have hn := timeCoefficient_diracCurrent_synthesis_nonneg c
  have hz : timeCoefficient (diracCurrent (synthesis c)) ≠ 0 :=
    fun h => hc ((timeCoefficient_diracCurrent_synthesis_eq_zero_iff c).mp h)
  exact lt_of_le_of_ne hn (Ne.symm hz)

/-- Encode the existing eight-field record in the actual native even algebra. -/
def encode (ψ : STASpinor) : ClPlus14 := synthesis (coefficients ψ)

@[simp] theorem encode_zero : encode zeroSpinor = 0 := by
  simp [encode]

theorem encode_injective : Function.Injective encode :=
  synthesis_injective.comp coefficients.injective

theorem encode_eq_zero_iff (ψ : STASpinor) : encode ψ = 0 ↔ ψ = zeroSpinor := by
  rw [encode, synthesis_eq_zero_iff, coefficients_eq_zero_iff]

/-- The full native sandwich of the encoded record is a Clifford vector. -/
theorem diracCurrent_encode_eq_iota (ψ : STASpinor) :
    diracCurrent (encode ψ) = ι14 (currentVector (coefficients ψ)) :=
  diracCurrent_synthesis_eq_iota (coefficients ψ)

/-- Vectority is membership in the range of the actual Clifford inclusion. -/
theorem diracCurrent_encode_mem_vector_range (ψ : STASpinor) :
    diracCurrent (encode ψ) ∈ LinearMap.range ι14 :=
  ⟨currentVector (coefficients ψ), (diracCurrent_encode_eq_iota ψ).symm⟩

/-- The displayed vector is uniquely determined by the native current. -/
theorem diracCurrent_encode_vector_unique (ψ : STASpinor) (v : V14)
    (hv : diracCurrent (encode ψ) = ι14 v) :
    v = currentVector (coefficients ψ) := by
  apply iota_injective
  exact hv.symm.trans (diracCurrent_encode_eq_iota ψ)

/-- The existing eight-square formula is the actual native current's time component. -/
theorem timeCoefficient_diracCurrent_encode (ψ : STASpinor) :
    timeCoefficient (diracCurrent (encode ψ)) = STASpinor.current_j0 ψ := by
  rw [encode, timeCoefficient_diracCurrent_synthesis, sum_sq_coefficients]

theorem timeCoefficient_diracCurrent_encode_nonneg (ψ : STASpinor) :
    0 ≤ timeCoefficient (diracCurrent (encode ψ)) := by
  rw [timeCoefficient_diracCurrent_encode]
  exact STASpinor.current_j0_nonneg ψ

theorem timeCoefficient_diracCurrent_encode_eq_zero_iff (ψ : STASpinor) :
    timeCoefficient (diracCurrent (encode ψ)) = 0 ↔ ψ = zeroSpinor := by
  rw [timeCoefficient_diracCurrent_encode]
  exact STASpinor.current_j0_zero_iff ψ

theorem diracCurrent_encode_eq_zero_iff (ψ : STASpinor) :
    diracCurrent (encode ψ) = 0 ↔ ψ = zeroSpinor := by
  rw [encode, diracCurrent_synthesis_eq_zero_iff, coefficients_eq_zero_iff]

theorem diracCurrent_encode_ne_zero {ψ : STASpinor} (hψ : ψ ≠ zeroSpinor) :
    diracCurrent (encode ψ) ≠ 0 :=
  fun h => hψ ((diracCurrent_encode_eq_zero_iff ψ).mp h)

theorem timeCoefficient_diracCurrent_encode_pos {ψ : STASpinor}
    (hψ : ψ ≠ zeroSpinor) :
    0 < timeCoefficient (diracCurrent (encode ψ)) := by
  apply timeCoefficient_diracCurrent_synthesis_pos
  intro h
  exact hψ ((coefficients_eq_zero_iff ψ).mp h)

end InfoGeometry.Canonical.HestenesSpinorCurrentBridge

end

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Ordinary Fermionic Primon Gas vs Graded Fermionic Index

This file separates two objects that must not be conflated.

* Ordinary fermionic primon gas: local factor `1 + x`, with positive
  occupations `0` or `1`.
* Graded fermionic index: local factor `1 - x`, obtained by inserting
  fermion parity `(-1)^F`.

For Euler products this is the finite algebraic core of

* `∏ₚ (1 + p^{-s}) = ζ(s) / ζ(2s)`;
* `∏ₚ (1 - p^{-s}) = 1 / ζ(s)`.

The reciprocal-index singularity statement is represented only as local
algebra: a zero of the denominator is the candidate singular location of the
reciprocal index.  No analytic continuation theorem or RH claim is asserted.
-/

noncomputable section

/-- Local bosonic Euler factor `(1-x)^{-1}`. -/
def bosonicLocalFactor (x : ℂ) : ℂ :=
  (1 - x)⁻¹

/-- Local ordinary fermion factor: occupation numbers `0` and `1`. -/
def ordinaryFermionLocalFactor (x : ℂ) : ℂ :=
  1 + x

/-- Local graded fermion index factor: parity insertion `(-1)^F`. -/
def gradedFermionLocalFactor (x : ℂ) : ℂ :=
  1 - x

/-- Ordinary fermions are the local `ζ(s)/ζ(2s)` ratio factor. -/
theorem ordinaryFermionLocal_as_zeta_ratio {x : ℂ} (hx : x ≠ 1) :
    ordinaryFermionLocalFactor x = (1 - x ^ 2) / (1 - x) := by
  have hfac : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  rw [ordinaryFermionLocalFactor, hfac]
  field_simp [hden]

/-- Graded fermion factor cancels the bosonic factor locally. -/
theorem gradedFermionLocal_cancels_boson {x : ℂ} (hx : x ≠ 1) :
    bosonicLocalFactor x * gradedFermionLocalFactor x = 1 := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  simp [bosonicLocalFactor, gradedFermionLocalFactor, hden]

/-- Same cancellation in the opposite order. -/
theorem boson_cancels_gradedFermionLocal {x : ℂ} (hx : x ≠ 1) :
    gradedFermionLocalFactor x * bosonicLocalFactor x = 1 := by
  rw [mul_comm]
  exact gradedFermionLocal_cancels_boson hx

/-- The graded index is the reciprocal of a chosen bosonic determinant. -/
def gradedIndexFromBoson (Z : ℂ → ℂ) (s : ℂ) : ℂ :=
  (Z s)⁻¹

/-- Candidate pole locations of the reciprocal index are zeros of the bosonic determinant. -/
def reciprocalIndexSingularity (Z : ℂ → ℂ) (s : ℂ) : Prop :=
  Z s = 0

theorem gradedIndex_singularity_iff_boson_zero (Z : ℂ → ℂ) (s : ℂ) :
    reciprocalIndexSingularity Z s ↔ Z s = 0 := by
  rfl

/--
If a bosonic determinant has a simple local zero `c*(s-s₀)`, its reciprocal
has the corresponding inverse local model.  This is algebraic only; it is not
an analytic proof that a given zeta zero is simple.
-/
theorem reciprocal_simple_zero_local_model
    {c s s₀ : ℂ} (hc : c ≠ 0) (hs : s ≠ s₀) :
    (c * (s - s₀))⁻¹ = c⁻¹ * (s - s₀)⁻¹ := by
  have hsub : s - s₀ ≠ 0 := sub_ne_zero.mpr hs
  field_simp [hc, hsub]

/-- At the bosonic pole model `1/(s-1)`, the reciprocal graded model is `s-1`. -/
def bosonicPoleModelIndex (s : ℂ) : ℂ :=
  (s - 1)⁻¹

def gradedZeroModelAtBosonicPole (s : ℂ) : ℂ :=
  s - 1

theorem graded_zero_model_cancels_bosonic_pole {s : ℂ} (hs : s ≠ 1) :
    bosonicPoleModelIndex s * gradedZeroModelAtBosonicPole s = 1 := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  simp [bosonicPoleModelIndex, gradedZeroModelAtBosonicPole, hsub]

/-- Consolidated ordinary/graded fermion distinction. -/
theorem fermionic_primon_index_synthesis :
    (∀ x : ℂ, x ≠ 1 →
      ordinaryFermionLocalFactor x = (1 - x ^ 2) / (1 - x)) ∧
    (∀ x : ℂ, x ≠ 1 →
      bosonicLocalFactor x * gradedFermionLocalFactor x = 1) ∧
    (∀ Z : ℂ → ℂ, ∀ s, reciprocalIndexSingularity Z s ↔ Z s = 0) ∧
    (∀ c s s₀ : ℂ, c ≠ 0 → s ≠ s₀ →
      (c * (s - s₀))⁻¹ = c⁻¹ * (s - s₀)⁻¹) ∧
    (∀ s : ℂ, s ≠ 1 →
      bosonicPoleModelIndex s * gradedZeroModelAtBosonicPole s = 1) := by
  exact ⟨fun x hx => ordinaryFermionLocal_as_zeta_ratio hx,
    fun x hx => gradedFermionLocal_cancels_boson hx,
    gradedIndex_singularity_iff_boson_zero,
    fun c s s₀ hc hs => reciprocal_simple_zero_local_model hc hs,
    fun s hs => graded_zero_model_cancels_bosonic_pole hs⟩

end noncomputable section

import InfoGeometry.Analysis.BipolarCrossRatioLog
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-!
# Exact differential behind the bipolar logarithm

This file extracts the branch-independent meromorphic differential carried by

`q(s) = s / (1 - s)`.

The global object is not the principal logarithm itself but its logarithmic
differential

`dlog01(s) = 1/s + 1/(1-s) = 1/(s(1-s))`.

It has principal part `+1/s` at `0` and `-1/(s-1)` at `1`.  Thus the two
punctures carry opposite residues.  This is the exact algebraic content behind
the informal source/sink and circulation language.

The principal `Complex.log` is used only locally, under an explicit slit-plane
hypothesis.  No global Hodge decomposition or claim that the twice-punctured
plane has a one-dimensional first de Rham cohomology is made here.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarLogDifferential

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-- Coefficient of the branch-independent logarithmic one-form `dq/q`. -/
def dlog01 (s : ℂ) : ℂ :=
  1 / s + 1 / (1 - s)

/-- Single rational denominator form of the same logarithmic differential. -/
theorem dlog01_eq_one_div_mul {s : ℂ} (hs : s ∈ punctured01) :
    dlog01 s = 1 / (s * (1 - s)) := by
  rcases hs with ⟨hs0, hs1⟩
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  unfold dlog01
  field_simp [hs0, h1s]
  ring

/-- The coefficient is symmetric under exchange of the two punctures.
The pulled-back one-form is nevertheless odd because `d(1-s) = -ds`. -/
theorem dlog01_one_sub (s : ℂ) :
    dlog01 (1 - s) = dlog01 s := by
  unfold dlog01
  ring_nf
  ring

/-- Complex conjugation preserves the real two-puncture logarithmic form. -/
theorem dlog01_conj (s : ℂ) :
    dlog01 (Complex.conj s) = Complex.conj (dlog01 s) := by
  simp [dlog01]

/-- Principal part at the puncture `0`: residue `+1`. -/
theorem dlog01_sub_origin_pole (s : ℂ) :
    dlog01 s - 1 / s = 1 / (1 - s) := by
  unfold dlog01
  ring

/-- Principal part at the puncture `1`: residue `-1`, written with local
coordinate `s-1`. -/
theorem dlog01_sub_one_pole (s : ℂ) :
    dlog01 s - (-1 / (s - 1)) = 1 / s := by
  unfold dlog01
  have h : 1 / (1 - s) = -1 / (s - 1) := by
    by_cases hs : s - 1 = 0
    · have : 1 - s = 0 := by linarith
      simp [hs, this]
    · have h1 : 1 - s ≠ 0 := by
        intro hzero
        apply hs
        linarith
      field_simp [hs, h1]
      ring
  rw [h]
  ring

/-- Ordered residue data of the two-pole logarithmic differential. -/
def residuePair : ℂ × ℂ := (1, -1)

@[simp] theorem residuePair_sum_zero : residuePair.1 + residuePair.2 = 0 := by
  simp [residuePair]

/-- Derivative of the canonical Möbius coordinate away from its pole. -/
theorem hasDerivAt_crossRatio01 {s : ℂ} (hs1 : s ≠ 1) :
    HasDerivAt crossRatio01 (1 / (1 - s) ^ 2) s := by
  unfold crossRatio01 cayleyToFugacity
  have hden : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hnum : HasDerivAt (fun z : ℂ => z) 1 s := hasDerivAt_id s
  have hdenDeriv : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
    simpa using (hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s)
  have hq := hnum.div hdenDeriv hden
  convert hq using 1
  field_simp [hden]
  ring

/-- On a compatible principal-log branch, the derivative of `W = log q`
is exactly the branch-independent rational differential `dlog01`. -/
theorem hasDerivAt_bipolarLog {s : ℂ}
    (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane) :
    HasDerivAt bipolarLog (dlog01 s) s := by
  have hq := hasDerivAt_crossRatio01 hs.2
  have hlog := (Complex.hasDerivAt_log hslit).comp s hq
  convert hlog using 1
  rw [dlog01_eq_one_div_mul hs]
  rcases hs with ⟨hs0, hs1⟩
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  unfold crossRatio01 cayleyToFugacity
  field_simp [hs0, h1s]
  ring

/-- Ordinary derivative readout of the local principal branch. -/
theorem deriv_bipolarLog {s : ℂ}
    (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane) :
    deriv bipolarLog s = dlog01 s := by
  exact (hasDerivAt_bipolarLog hs hslit).deriv

/-- The involution `s ↦ 1-s` reverses the logarithmic one-form after including
the derivative of the coordinate involution. -/
theorem pullback_one_sub_dlog01 (s : ℂ) :
    (-1 : ℂ) * dlog01 (1 - s) = -dlog01 s := by
  rw [dlog01_one_sub]
  ring

end InfoGeometry.Analysis.BipolarLogDifferential

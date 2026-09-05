import InfoGeometry.Analysis.BipolarCrossRatioLog
import Mathlib.Tactic

/-!
# Möbius equivalence of the bipolar punctured coordinate charts

The rational function `q(s) = s / (1 - s)` is a Möbius coordinate. On the
affine twice-punctured plane it gives an equivalence

`C \ {0,1}  ≃  C \ {0,-1}`

with inverse `z ↦ z / (1 + z)`.

This is the exact finite conformal statement behind the informal
"uniformizing coordinate" language. It is not the universal covering of the
thrice-punctured sphere; a modular-lambda or Fuchsian-group uniformization is a
separate global theorem requiring additional analytic and group-theoretic
infrastructure.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarMobiusPunctureEquiv

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-- Target affine chart, with the images of `0` and `infinity` removed. -/
def punctured0NegOne : Set ℂ := {z | z ≠ 0 ∧ z ≠ -1}

/-- Source twice-punctured affine chart. -/
abbrev SourcePoint := {s : ℂ // s ∈ punctured01}

/-- Target twice-punctured affine chart. -/
abbrev TargetPoint := {z : ℂ // z ∈ punctured0NegOne}

/-- Rational inverse of `q(s) = s / (1-s)`. -/
def inverseCrossRatio01 (z : ℂ) : ℂ := z / (1 + z)

lemma one_add_ne_zero_of_mem {z : ℂ} (hz : z ∈ punctured0NegOne) :
    1 + z ≠ 0 := by
  intro h
  apply hz.2
  have h' : z + 1 = 0 := by simpa [add_comm] using h
  calc
    z = (z + 1) - 1 := by ring
    _ = 0 - 1 := by rw [h']
    _ = -1 := by ring

/-- The bipolar Möbius coordinate avoids both target punctures. -/
theorem crossRatio01_mem_punctured0NegOne
    {s : ℂ} (hs : s ∈ punctured01) :
    crossRatio01 s ∈ punctured0NegOne := by
  constructor
  · exact crossRatio01_ne_zero hs
  · intro hneg
    have hden : 1 - s ≠ 0 := one_sub_ne_zero_of_mem hs
    have hquot : s / (1 - s) = (-1 : ℂ) := by
      simpa [crossRatio01, cayleyToFugacity] using hneg
    have hmul : s = (-1 : ℂ) * (1 - s) :=
      (div_eq_iff hden).mp hquot
    have h10 : (1 : ℂ) = 0 := by
      calc
        1 = s - ((-1 : ℂ) * (1 - s)) := by ring
        _ = 0 := sub_eq_zero.mpr hmul
    exact one_ne_zero h10

/-- The inverse Möbius coordinate avoids `0` and `1`. -/
theorem inverseCrossRatio01_mem_punctured01
    {z : ℂ} (hz : z ∈ punctured0NegOne) :
    inverseCrossRatio01 z ∈ punctured01 := by
  have hden : 1 + z ≠ 0 := one_add_ne_zero_of_mem hz
  constructor
  · exact div_ne_zero hz.1 hden
  · intro h1
    have hquot : z / (1 + z) = (1 : ℂ) := by
      simpa [inverseCrossRatio01] using h1
    have hmul : z = 1 * (1 + z) :=
      (div_eq_iff hden).mp hquot
    have hmul' : z = 1 + z := by simpa using hmul
    have h10 : (1 : ℂ) = 0 := by
      calc
        1 = (1 + z) - z := by ring
        _ = 0 := sub_eq_zero.mpr hmul'.symm
    exact one_ne_zero h10

/-- Useful denominator identity for the inverse calculation. -/
theorem one_add_crossRatio01
    {s : ℂ} (hs : s ∈ punctured01) :
    1 + crossRatio01 s = (1 - s)⁻¹ := by
  have hden : 1 - s ≠ 0 := one_sub_ne_zero_of_mem hs
  unfold crossRatio01 cayleyToFugacity
  field_simp [hden]
  ring

/-- Useful denominator identity in the opposite direction. -/
theorem one_sub_inverseCrossRatio01
    {z : ℂ} (hz : z ∈ punctured0NegOne) :
    1 - inverseCrossRatio01 z = (1 + z)⁻¹ := by
  have hden : 1 + z ≠ 0 := one_add_ne_zero_of_mem hz
  unfold inverseCrossRatio01
  field_simp [hden]
  ring

/-- The proposed inverse is a left inverse on the punctured source chart. -/
theorem inverseCrossRatio01_crossRatio01
    {s : ℂ} (hs : s ∈ punctured01) :
    inverseCrossRatio01 (crossRatio01 s) = s := by
  rw [inverseCrossRatio01, one_add_crossRatio01 hs, div_inv]
  unfold crossRatio01 cayleyToFugacity
  exact div_mul_cancel₀ s (one_sub_ne_zero_of_mem hs)

/-- The proposed inverse is a right inverse on the punctured target chart. -/
theorem crossRatio01_inverseCrossRatio01
    {z : ℂ} (hz : z ∈ punctured0NegOne) :
    crossRatio01 (inverseCrossRatio01 z) = z := by
  change inverseCrossRatio01 z / (1 - inverseCrossRatio01 z) = z
  rw [one_sub_inverseCrossRatio01 hz, div_inv]
  unfold inverseCrossRatio01
  exact div_mul_cancel₀ z (one_add_ne_zero_of_mem hz)

/-- The exact Möbius equivalence between the two affine presentations of the
thrice-punctured sphere. -/
def mobiusPunctureEquiv : SourcePoint ≃ TargetPoint where
  toFun s :=
    ⟨crossRatio01 (s : ℂ), crossRatio01_mem_punctured0NegOne s.property⟩
  invFun z :=
    ⟨inverseCrossRatio01 (z : ℂ), inverseCrossRatio01_mem_punctured01 z.property⟩
  left_inv s := by
    apply Subtype.ext
    exact inverseCrossRatio01_crossRatio01 s.property
  right_inv z := by
    apply Subtype.ext
    exact crossRatio01_inverseCrossRatio01 z.property

@[simp] theorem mobiusPunctureEquiv_apply (s : SourcePoint) :
    (mobiusPunctureEquiv s : ℂ) = crossRatio01 (s : ℂ) := rfl

@[simp] theorem mobiusPunctureEquiv_symm_apply (z : TargetPoint) :
    ((mobiusPunctureEquiv.symm z : SourcePoint) : ℂ) =
      inverseCrossRatio01 (z : ℂ) := rfl

/-- Compact exact-coordinate packet. -/
theorem bipolar_mobius_puncture_equiv_packet
    (s : SourcePoint) (z : TargetPoint) :
    inverseCrossRatio01 (crossRatio01 (s : ℂ)) = (s : ℂ) ∧
      crossRatio01 (inverseCrossRatio01 (z : ℂ)) = (z : ℂ) := by
  exact ⟨inverseCrossRatio01_crossRatio01 s.property,
    crossRatio01_inverseCrossRatio01 z.property⟩

end InfoGeometry.Analysis.BipolarMobiusPunctureEquiv

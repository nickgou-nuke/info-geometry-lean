/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Superalgebra.MadelungNonassociativeVortexSmoothness

/-!
# Witten--Möbius parity square on the existing split-octonion carrier

This file reuses the split-octonion product owned by
`MadelungNonassociativeVortexSmoothness`. It proves the square of the specified
algebra element and the exact condition for involutivity on the real unit
circle when `s ≠ 0`. The diagonal readout is recorded as a formula; no
Hilbert-space Witten index, EPR state, or topological protection is asserted.
-/

namespace InfoGeometry.Superalgebra.WittenMoebiusParity

open InfoGeometry.Superalgebra.MadelungNonassociativeVortex

variable {R : Type*} [CommRing R]

/-- The proposed chiral parity element, expressed in the existing carrier. -/
def parityElement (c s : R) (u v : ColorVec3 R) : SplitOctonion R :=
  SplitOctonion.sub
    (SplitOctonion.scale c SplitOctonion.paraSymplecticK0)
    (SplitOctonion.scale s
      (SplitOctonion.sub (SplitOctonion.quark u) (SplitOctonion.antiquark v)))

/-- Exact square formula: the scalar coefficient is controlled by `u · v`. -/
theorem parityElement_sq (c s : R) (u v : ColorVec3 R) :
    SplitOctonion.mul (parityElement c s u v) (parityElement c s u v) =
      SplitOctonion.scale (c ^ 2 - s ^ 2 * ColorVec3.dot u v) SplitOctonion.one := by
  dsimp [parityElement, SplitOctonion.paraSymplecticK0, SplitOctonion.quark,
    SplitOctonion.antiquark, SplitOctonion.mul, SplitOctonion.sub,
    SplitOctonion.scale, SplitOctonion.one, ColorVec3.zero, ColorVec3.dot,
    ColorVec3.sub, ColorVec3.smul, ColorVec3.cross]
  apply SplitOctonion.ext
  · simp [SplitOctonion.mul, SplitOctonion.scale, SplitOctonion.sub, SplitOctonion.one, SplitOctonion.paraSymplecticK0, SplitOctonion.quark, SplitOctonion.antiquark, ColorVec3.dot, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross]; ring
  · apply ColorVec3.ext <;> simp [SplitOctonion.mul, SplitOctonion.scale, SplitOctonion.sub, ColorVec3.add, ColorVec3.dot, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring
  · apply ColorVec3.ext <;> simp [SplitOctonion.mul, SplitOctonion.scale, SplitOctonion.sub, ColorVec3.add, ColorVec3.dot, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross] <;> ring
  · simp [SplitOctonion.mul, SplitOctonion.scale, SplitOctonion.sub, SplitOctonion.one, SplitOctonion.paraSymplecticK0, SplitOctonion.quark, SplitOctonion.antiquark, ColorVec3.dot, ColorVec3.sub, ColorVec3.smul, ColorVec3.cross]; ring

/-- The unit-circle and pairing conditions suffice for the parity element to square to one. -/
theorem parityElement_involutive_of_unitCircle_pairing
    (c s : R) (u v : ColorVec3 R)
    (h_circle : c ^ 2 + s ^ 2 = 1)
    (h_pairing : ColorVec3.dot u v = -1) :
    SplitOctonion.mul (parityElement c s u v) (parityElement c s u v) =
      SplitOctonion.one := by
  rw [parityElement_sq]
  have h_coeff : c ^ 2 - s ^ 2 * ColorVec3.dot u v = 1 := by
    rw [h_pairing]
    linear_combination h_circle
  rw [h_coeff]
  simp [SplitOctonion.scale, SplitOctonion.one, ColorVec3.smul, ColorVec3.zero]

/-- Conversely, on the real unit circle a nonzero `s` forces the pairing to be `-1`. -/
theorem pairing_eq_neg_one_of_involutive
    (c s : ℝ) (u v : ColorVec3 ℝ)
    (h_circle : c ^ 2 + s ^ 2 = 1)
    (hs : s ≠ 0)
    (h_involutive :
      SplitOctonion.mul (parityElement c s u v) (parityElement c s u v) =
        SplitOctonion.one) :
    ColorVec3.dot u v = -1 := by
  have h_coeff : c ^ 2 - s ^ 2 * ColorVec3.dot u v = 1 := by
    have h := congrArg SplitOctonion.a h_involutive
    rw [parityElement_sq] at h
    simpa [SplitOctonion.scale, SplitOctonion.one, ColorVec3.smul,
      ColorVec3.zero] using h
  have h_product : s ^ 2 * (ColorVec3.dot u v + 1) = 0 := by
    nlinarith [h_coeff, h_circle]
  rcases mul_eq_zero.mp h_product with h_s2 | h_pair
  · exact False.elim ((pow_ne_zero 2 hs) h_s2)
  · linarith

/-- The diagonal difference readout of this element is `2*c` (not a constant in `c`). -/
def diagonalParityReadout (x : SplitOctonion R) : R := x.a - x.b

theorem diagonalParityReadout_parityElement (c s : R) (u v : ColorVec3 R) :
    diagonalParityReadout (parityElement c s u v) = 2 * c := by
  dsimp [diagonalParityReadout, parityElement, SplitOctonion.paraSymplecticK0,
    SplitOctonion.quark, SplitOctonion.antiquark, SplitOctonion.sub,
    SplitOctonion.scale, ColorVec3.zero, ColorVec3.sub, ColorVec3.smul]
  ring

/-! ## Angular periodicity on the existing parity element -/

/-- With the standard angular parametrization, the parity element is
antiperiodic under a half-turn.  This is the algebraic statement that remains
valid before passing to any projective quotient. -/
theorem parityElement_antiperiodic (θ : ℝ) (u v : ColorVec3 ℝ) :
    parityElement (Real.cos (θ + Real.pi)) (Real.sin (θ + Real.pi)) u v =
      SplitOctonion.scale (-1)
        (parityElement (Real.cos θ) (Real.sin θ) u v) := by
  rw [Real.cos_add_pi, Real.sin_add_pi]
  dsimp [parityElement, SplitOctonion.paraSymplecticK0,
    SplitOctonion.quark, SplitOctonion.antiquark, SplitOctonion.sub,
    SplitOctonion.scale, SplitOctonion.one, ColorVec3.zero,
    ColorVec3.sub, ColorVec3.smul]
  apply SplitOctonion.ext
  · ring
  · apply ColorVec3.ext <;> ring
  · apply ColorVec3.ext <;> ring
  · ring

end InfoGeometry.Superalgebra.WittenMoebiusParity

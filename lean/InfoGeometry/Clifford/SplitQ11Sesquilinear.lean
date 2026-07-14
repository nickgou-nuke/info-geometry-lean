import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Clifford.SplitQ11Equivariance
import Mathlib.Data.Complex.Basic

/-!
# InfoGeometry.Clifford.SplitQ11Sesquilinear

Minimal sesquilinear readback on the complexification of the split `(1,1)` lane.

This file adds an explicit complex sesquilinear pairing whose real restriction
recovers the existing split bilinear/quadratic forms from `SplitQ11`.
No new witness packet and no placeholder theorem.
-/

noncomputable section

namespace SplitQ11Sesquilinear

open InfoGeometry.Clifford

abbrev CSplit11 := ℂ × ℂ

/-- Complexified split `(1,1)` sesquilinear pairing. -/
def splitSesq11 (z w : CSplit11) : ℂ :=
  star z.1 * w.1 - star z.2 * w.2

@[simp] theorem splitSesq11_apply (z w : CSplit11) :
    splitSesq11 z w = star z.1 * w.1 - star z.2 * w.2 := rfl

@[simp] theorem splitSesq11_add_left (z₁ z₂ w : CSplit11) :
    splitSesq11 (z₁ + z₂) w = splitSesq11 z₁ w + splitSesq11 z₂ w := by
  rcases z₁ with ⟨a1, a2⟩
  rcases z₂ with ⟨b1, b2⟩
  rcases w with ⟨c1, c2⟩
  simp [splitSesq11]
  ring

@[simp] theorem splitSesq11_add_right (z w₁ w₂ : CSplit11) :
    splitSesq11 z (w₁ + w₂) = splitSesq11 z w₁ + splitSesq11 z w₂ := by
  rcases z with ⟨a1, a2⟩
  rcases w₁ with ⟨b1, b2⟩
  rcases w₂ with ⟨c1, c2⟩
  simp [splitSesq11]
  ring

@[simp] theorem splitSesq11_smul_left (c : ℂ) (z w : CSplit11) :
    splitSesq11 (c • z) w = star c * splitSesq11 z w := by
  rcases z with ⟨a1, a2⟩
  rcases w with ⟨b1, b2⟩
  simp [splitSesq11]
  ring

@[simp] theorem splitSesq11_smul_right (c : ℂ) (z w : CSplit11) :
    splitSesq11 z (c • w) = c * splitSesq11 z w := by
  rcases z with ⟨a1, a2⟩
  rcases w with ⟨b1, b2⟩
  simp [splitSesq11]
  ring

/-- Conjugate symmetry of the split sesquilinear pairing. -/
@[simp] theorem splitSesq11_star_swap (z w : CSplit11) :
    star (splitSesq11 z w) = splitSesq11 w z := by
  rcases z with ⟨a1, a2⟩
  rcases w with ⟨b1, b2⟩
  simp [splitSesq11]
  ring

/-- Real vectors embedded into the complexified split lane. -/
def ofRealSplit11 (x : ℝ × ℝ) : CSplit11 := ((x.1 : ℂ), (x.2 : ℂ))

/-- On real vectors, the sesquilinear pairing recovers `splitB11`. -/
@[simp] theorem splitSesq11_ofReal (x y : ℝ × ℝ) :
    splitSesq11 (ofRealSplit11 x) (ofRealSplit11 y) = (splitB11 x y : ℂ) := by
  rcases x with ⟨x1, x2⟩
  rcases y with ⟨y1, y2⟩
  simp [ofRealSplit11, splitSesq11, splitB11_apply]

/-- Diagonal real part on real vectors recovers the split quadratic form. -/
@[simp] theorem splitSesq11_diag_re_ofReal_eq_splitQ11 (x : ℝ × ℝ) :
    Complex.re (splitSesq11 (ofRealSplit11 x) (ofRealSplit11 x)) = splitQ11 x := by
  rcases x with ⟨x1, x2⟩
  simp [splitSesq11, splitQ11_apply, ofRealSplit11]

/-- Identity-scaling compatibility (base equivariance sanity check). -/
@[simp] theorem splitSesq11_one_smul (z w : CSplit11) :
    splitSesq11 ((1 : ℂ) • z) ((1 : ℂ) • w) = splitSesq11 z w := by
  simp [splitSesq11]

/--
Unit-modulus phase-equivariance: the split sesquilinear pairing is invariant
under global complex scaling by any phase of norm one.

`S(cz, cw) = star c * c * S(z, w) = 1 * S(z, w)`.
-/
theorem splitSesq11_unit_modulus_smul
    (c : ℂ) (hc : star c * c = 1) (z w : CSplit11) :
    splitSesq11 (c • z) (c • w) = splitSesq11 z w := by
  rw [splitSesq11_smul_left, splitSesq11_smul_right, ← mul_assoc, hc, one_mul]

end SplitQ11Sesquilinear

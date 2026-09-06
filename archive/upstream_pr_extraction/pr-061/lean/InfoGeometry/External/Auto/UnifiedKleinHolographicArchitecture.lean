import Mathlib.Tactic

/-!
# Unified Klein holographic architecture

This file records a concrete finite/integer algebraic core:

* a nonsymmorphic glide on `ℤ × ℤ`;
* the square of the glide is a translation;
* the linear part reverses orientation;
* the half-turn phase has square `1`;
* the finite `Z₂` cocycle twist is XOR.
-/

namespace UnifiedKleinHolographicArchitecture

abbrev LatticePoint := ℤ × ℤ

def translationX (p : LatticePoint) : LatticePoint :=
  (p.1 + 2, p.2)

def glide (p : LatticePoint) : LatticePoint :=
  (p.1 + 1, -p.2)

def reflectionLinearPart (p : LatticePoint) : LatticePoint :=
  (p.1, -p.2)

theorem glide_sq_eq_translation (p : LatticePoint) :
    glide (glide p) = translationX p := by
  ext
  · simp [glide, translationX]
    omega
  · simp [glide, translationX]

theorem reflection_linear_part_involutive (p : LatticePoint) :
    reflectionLinearPart (reflectionLinearPart p) = p := by
  ext <;> simp [reflectionLinearPart]

theorem reflection_orientation_det :
    ((1 : ℤ) * (-1) - (0 : ℤ) * 0) = -1 := by
  ring

def ribbonHalfTurn : ℤ := -1

theorem ribbon_half_turn_square :
    ribbonHalfTurn * ribbonHalfTurn = 1 := by
  norm_num [ribbonHalfTurn]

def spinLogHalfSpectrum : ℚ := 1 / 2

theorem spin_log_half_spectrum_doubles :
    2 * spinLogHalfSpectrum = 1 := by
  norm_num [spinLogHalfSpectrum]

def z2Twist (a b : Bool) : Bool :=
  xor a b

theorem z2Twist_self_cancel (a : Bool) :
    z2Twist a a = false := by
  cases a <;> rfl

theorem z2Twist_comm (a b : Bool) :
    z2Twist a b = z2Twist b a := by
  cases a <;> cases b <;> rfl

theorem z2Twist_assoc (a b c : Bool) :
    z2Twist (z2Twist a b) c = z2Twist a (z2Twist b c) := by
  cases a <;> cases b <;> cases c <;> rfl

end UnifiedKleinHolographicArchitecture

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.Ring

/-!
# Writhe normalization of a bracket

This module proves the algebraic cancellation behind writhe normalization.
It does not construct knot diagrams, a bracket, a Markov trace, or a Jones
polynomial; those must be supplied by a separate owner.
-/

namespace InfoGeometry.Topological.JonesPolynomial

/-! ## Temperley--Lieb crossing convention -/

/-- The chosen Kauffman--Temperley--Lieb crossing element
`A * e + A⁻¹ * 1`.  This fixes the positive-crossing convention used by the
finite braid layer; the corresponding braid relations require the usual
Temperley--Lieb relations on the elements `e`. -/
def temperleyLiebBraidGenerator {R : Type*} [Ring R]
    (A : Units R) (e : R) : R :=
  (A : R) * e + ((A⁻¹ : Units R) : R)

@[simp]
theorem temperleyLiebBraidGenerator_zero {R : Type*} [Ring R]
    (A : Units R) :
    temperleyLiebBraidGenerator A (0 : R) = ((A⁻¹ : Units R) : R) := by
  simp [temperleyLiebBraidGenerator]

theorem temperleyLiebBraidGenerator_def {R : Type*} [Ring R]
    (A : Units R) (e : R) :
    temperleyLiebBraidGenerator A e =
      (A : R) * e + ((A⁻¹ : Units R) : R) := by
  rfl

/-- Integer powers of a Reidemeister-I factor cancel its bracket scaling. -/
theorem reidemeister_factor_cancel {R : Type*} [Group R]
    (c : R) (w : ℤ) :
    c ^ (-(w + 1)) * c = c ^ (-w) := by
  rw [show -(w + 1) = -w + (-1) by ring, zpow_add]
  simp

/-- The normalized bracket associated with a unit crossing factor. -/
def normalizedBracket {D R : Type*} [CommRing R]
    (c : Units R) (bracket : D → R) (writhe : D → ℤ) (d : D) : R :=
  ((c ^ (-writhe d) : Units R) : R) * bracket d

/-- A Reidemeister-I bracket law is cancelled by writhe normalization. -/
theorem normalizedBracket_reidemeister_one
    {D R : Type*} [CommRing R]
    (c : Units R) (bracket : D → R) (writhe : D → ℤ)
    (move : D → D)
    (hbracket : ∀ d, bracket (move d) = (c : R) * bracket d)
    (hwrithe : ∀ d, writhe (move d) = writhe d + 1) (d : D) :
    normalizedBracket c bracket writhe (move d) =
      normalizedBracket c bracket writhe d := by
  unfold normalizedBracket
  rw [hbracket d, hwrithe d]
  have hpow : (c ^ (-(writhe d + 1)) : Units R) =
      c ^ (-writhe d) * c⁻¹ := by
    rw [show -(writhe d + 1) = -writhe d + (-1) by ring,
      zpow_add, zpow_neg, zpow_one]
  rw [hpow]
  simp [Units.val_mul, mul_assoc]

end InfoGeometry.Topological.JonesPolynomial

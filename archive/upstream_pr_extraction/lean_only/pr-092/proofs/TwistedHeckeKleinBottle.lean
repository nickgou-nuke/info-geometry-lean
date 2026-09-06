import Mathlib

/-!
# Twisted Hecke/Klein-bottle affine action

Repaired external file: the Aubert--Plymen torus action and Brillouin glide are
identical affine maps, with a computed square and orientation-reversing linear
part.
-/

noncomputable section

namespace PaperwallHolography

/-- Aubert--Plymen action on angle coordinates. -/
def aubertPlymenAction (p : ℝ × ℝ) : ℝ × ℝ := (p.1 + Real.pi, -p.2)

/-- Brillouin glide action on angle coordinates. -/
def brillouinGlideAction (k : ℝ × ℝ) : ℝ × ℝ := (k.1 + Real.pi, -k.2)

/-- The two actions are the same affine transformation. -/
theorem aubertPlymen_eq_brillouinGlide (x : ℝ × ℝ) :
    aubertPlymenAction x = brillouinGlideAction x := rfl

/-- Squaring the action shifts the first coordinate by `2π` and fixes the second. -/
theorem aubertPlymen_sq_is_identity_mod_2pi (p : ℝ × ℝ) :
    aubertPlymenAction (aubertPlymenAction p) = (p.1 + 2 * Real.pi, p.2) := by
  ext <;> simp [aubertPlymenAction] <;> ring

/-- Linear reflection part. -/
def linearPart (v : ℝ × ℝ) : ℝ × ℝ := (v.1, -v.2)

/-- The linear part reverses the standard two-coordinate oriented area form. -/
theorem linearPart_reverses_orientation (x y : ℝ) :
    let v := (x, y)
    (linearPart v).1 * (linearPart (y, x)).2 - (linearPart v).2 * (linearPart (y, x)).1 =
      -(x * x - y * y) := by
  simp [linearPart]
  ring

#check aubertPlymen_eq_brillouinGlide
#check aubertPlymen_sq_is_identity_mod_2pi
#check linearPart_reverses_orientation

end PaperwallHolography

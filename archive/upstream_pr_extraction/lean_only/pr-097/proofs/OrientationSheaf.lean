import Mathlib
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Space/Time Orientability Characters and the Orientation Sheaf
-/

section SpaceTimeOrientation

variable {G : Type*} [Group G]

/-- The space orientation character `σ_plus`. -/
def sigma_plus (f : G →* Units ℤ) : G →* Units ℤ := f

/-- The time orientation character `σ_minus`. -/
def sigma_minus (g : G →* Units ℤ) : G →* Units ℤ := g

/-- The total orientation character `σ = σ_plus * σ_minus`. -/
def sigma (f g : G →* Units ℤ) : G →* Units ℤ := f * g

lemma sigma_apply (f g : G →* Units ℤ) (x : G) : 
    sigma f g x = sigma_plus f x * sigma_minus g x := by
  rfl

end SpaceTimeOrientation

section OrientationSheaf

variable {X : Type*}

/-- A local section of the orientation sheaf as a function from a subset to `Units ℤ`. -/
structure OrientationSection (U : Set X) where
  val : U → Units ℤ

end OrientationSheaf

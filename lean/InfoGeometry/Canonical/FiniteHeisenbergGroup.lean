import InfoGeometry.Canonical.FiniteHeisenbergCore
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The finite Heisenberg group structure

`FiniteHeisenbergCore` supplies the coordinate multiplication and its
identities.  The raw carrier is a product and therefore already has the
componentwise product instance; this owner uses a thin wrapper so that the
Heisenberg cocycle becomes the native group multiplication without an
instance collision.
-/

namespace InfoGeometry.Canonical.FiniteHeisenbergCore

structure FiniteHeisenberg (n : ℕ) where
  coord : Heisenberg n

def finiteHeisenbergMul {n : ℕ} (x y : FiniteHeisenberg n) : FiniteHeisenberg n :=
  ⟨heisenbergMul x.coord y.coord⟩

def finiteHeisenbergOne {n : ℕ} : FiniteHeisenberg n :=
  ⟨heisenbergOne⟩

def finiteHeisenbergInv {n : ℕ} (x : FiniteHeisenberg n) : FiniteHeisenberg n :=
  ⟨heisenbergInv x.coord⟩

instance finiteHeisenbergGroup (n : ℕ) : Group (FiniteHeisenberg n) where
  mul := finiteHeisenbergMul
  one := finiteHeisenbergOne
  inv := finiteHeisenbergInv
  mul_assoc := by
    intro x y z
    cases x; cases y; cases z
    apply congrArg FiniteHeisenberg.mk
    exact heisenberg_assoc _ _ _
  one_mul := by
    intro x
    cases x
    apply congrArg FiniteHeisenberg.mk
    exact heisenberg_one_mul _
  mul_one := by
    intro x
    cases x
    apply congrArg FiniteHeisenberg.mk
    exact heisenberg_mul_one _
  inv_mul_cancel := by
    intro x
    cases x
    apply congrArg FiniteHeisenberg.mk
    exact heisenberg_inv_mul _

@[simp] theorem finiteHeisenberg_mul_coord (x y : FiniteHeisenberg n) :
    (x * y).coord = heisenbergMul x.coord y.coord := rfl

@[simp] theorem finiteHeisenberg_one_coord :
    (1 : FiniteHeisenberg n).coord = heisenbergOne := rfl

@[simp] theorem finiteHeisenberg_inv_coord (x : FiniteHeisenberg n) :
    (x⁻¹).coord = heisenbergInv x.coord := rfl

def finiteHeisenbergCenterElement {n : ℕ} (c : ZMod n) : FiniteHeisenberg n :=
  ⟨heisenbergCenterElement c⟩

/-- The group commutator is the central cocycle defect. -/
theorem finiteHeisenberg_group_commutator (x y : FiniteHeisenberg n) :
    x * y * x⁻¹ * y⁻¹ =
      finiteHeisenbergCenterElement
        (x.coord.1.1 * y.coord.1.2 - y.coord.1.1 * x.coord.1.2) := by
  cases x with
  | mk x =>
    cases y with
    | mk y =>
      rcases x with ⟨⟨a, b⟩, c⟩
      rcases y with ⟨⟨d, e⟩, f⟩
      change finiteHeisenbergMul
          (finiteHeisenbergMul
            (finiteHeisenbergMul
              ⟨⟨⟨a, b⟩, c⟩⟩ ⟨⟨⟨d, e⟩, f⟩⟩)
            (finiteHeisenbergInv ⟨⟨⟨a, b⟩, c⟩⟩))
          (finiteHeisenbergInv ⟨⟨⟨d, e⟩, f⟩⟩) = _
      apply congrArg FiniteHeisenberg.mk
      simp [finiteHeisenbergMul, finiteHeisenbergInv,
        heisenbergMul, heisenbergInv, heisenbergCenterElement]
      ring

/-- Central coordinates commute with every finite Heisenberg element. -/
theorem finiteHeisenberg_center_commutes (c : ZMod n) (x : FiniteHeisenberg n) :
    Commute (finiteHeisenbergCenterElement c) x := by
  change finiteHeisenbergMul (finiteHeisenbergCenterElement c) x =
    finiteHeisenbergMul x (finiteHeisenbergCenterElement c)
  apply congrArg FiniteHeisenberg.mk
  exact heisenberg_center_mul c x.coord

end InfoGeometry.Canonical.FiniteHeisenbergCore

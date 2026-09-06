import Mathlib

/-!
# Finite Heisenberg carriers

The finite Heisenberg group over `ZMod n` is represented by triples with the
standard cocycle term `a * b'`.  This is the exponentiated Weyl layer; it is
not the characteristic-zero Weyl algebra with additive CCR.
-/

namespace InfoGeometry.Canonical.FiniteHeisenbergCore

/-- Coordinates for the finite Heisenberg group over `ZMod n`. -/
abbrev Heisenberg (n : ℕ) := (ZMod n × ZMod n) × ZMod n

/-- The Heisenberg multiplication, including the central cocycle. -/
def heisenbergMul {n : ℕ} (x y : Heisenberg n) : Heisenberg n :=
  ((x.1.1 + y.1.1, x.1.2 + y.1.2), x.2 + y.2 + x.1.1 * y.1.2)

/-- The identity coordinate. -/
def heisenbergOne {n : ℕ} : Heisenberg n := ((0, 0), 0)

/-- The inverse coordinate. -/
def heisenbergInv {n : ℕ} (x : Heisenberg n) : Heisenberg n :=
  ((-x.1.1, -x.1.2), -x.2 + x.1.1 * x.1.2)

theorem heisenberg_mul_def {n : ℕ} (x y : Heisenberg n) :
    heisenbergMul x y = ((x.1.1 + y.1.1, x.1.2 + y.1.2),
      x.2 + y.2 + x.1.1 * y.1.2) := rfl

theorem heisenberg_assoc {n : ℕ} (x y z : Heisenberg n) :
    heisenbergMul (heisenbergMul x y) z =
      heisenbergMul x (heisenbergMul y z) := by
  rcases x with ⟨⟨a, b⟩, c⟩
  rcases y with ⟨⟨d, e⟩, f⟩
  rcases z with ⟨⟨g, h⟩, i⟩
  ext <;> simp [heisenbergMul] <;> ring

theorem heisenberg_one_mul {n : ℕ} (x : Heisenberg n) :
    heisenbergMul heisenbergOne x = x := by
  rcases x with ⟨⟨a, b⟩, c⟩
  simp [heisenbergMul, heisenbergOne]

theorem heisenberg_mul_one {n : ℕ} (x : Heisenberg n) :
    heisenbergMul x heisenbergOne = x := by
  rcases x with ⟨⟨a, b⟩, c⟩
  simp [heisenbergMul, heisenbergOne]

theorem heisenberg_inv_mul {n : ℕ} (x : Heisenberg n) :
    heisenbergMul (heisenbergInv x) x = heisenbergOne := by
  rcases x with ⟨⟨a, b⟩, c⟩
  ext <;> simp [heisenbergMul, heisenbergInv, heisenbergOne]

theorem heisenberg_mul_inv {n : ℕ} (x : Heisenberg n) :
    heisenbergMul x (heisenbergInv x) = heisenbergOne := by
  rcases x with ⟨⟨a, b⟩, c⟩
  ext <;> simp [heisenbergMul, heisenbergInv, heisenbergOne]

/-- The central coordinate subgroup, written as explicit central elements. -/
def heisenbergCenterElement {n : ℕ} (c : ZMod n) : Heisenberg n := ((0, 0), c)

theorem heisenberg_center_mul {n : ℕ} (c : ZMod n) (x : Heisenberg n) :
    heisenbergMul (heisenbergCenterElement c) x =
      heisenbergMul x (heisenbergCenterElement c) := by
  rcases x with ⟨⟨a, b⟩, d⟩
  simp [heisenbergCenterElement, heisenbergMul, add_comm]

theorem heisenberg_cocycle_defect {n : ℕ} (x y : Heisenberg n) :
    (heisenbergMul x y).2 - (heisenbergMul y x).2 =
      x.1.1 * y.1.2 - y.1.1 * x.1.2 := by
  change (x.2 + y.2 + x.1.1 * y.1.2) -
      (y.2 + x.2 + y.1.1 * x.1.2) = _
  ring

theorem card_heisenberg (n : ℕ) [Fintype (ZMod n)] :
    Fintype.card (Heisenberg n) = n ^ 3 := by
  simp [Heisenberg, ZMod.card]
  ring

theorem card_heisenberg_two : Fintype.card (Heisenberg 2) = 8 := by
  simpa using card_heisenberg 2

theorem card_heisenberg_three : Fintype.card (Heisenberg 3) = 27 := by
  simpa using card_heisenberg 3

theorem card_heisenberg_six : Fintype.card (Heisenberg 6) = 216 := by
  simpa using card_heisenberg 6

end InfoGeometry.Canonical.FiniteHeisenbergCore

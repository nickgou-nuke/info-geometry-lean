/-
# SuperLieRing.lean

ℤ₂-graded Lie superalgebra over ℝ (typeclass).

Extends `SuperBracket` with:
- ℤ₂-grading via `evenPart` / `oddPart` ℝ-submodules
- Graded anti-commutativity (even-even / even-odd skew, odd-odd symmetric)
- Super Jacobi identity by parity sectors
-/
import Mathlib
import InfoGeometry.Algebra.SuperBracket

set_option linter.dupNamespace false

noncomputable section

namespace InfoGeometry.Algebra

/--
A **super Lie ring** over ℝ is an `AddCommGroup` with `Module ℝ` and an
ℝ-bilinear bracket `⁅·,·⁆` together with a ℤ₂-grading by two ℝ-submodules
(`evenPart` and `oddPart`) such that for **homogeneous** elements:

1. **Graded anti-commutativity**:
   - even–even / even–odd / odd–even: `⁅x,y⁆ = -⁅y,x⁆`
   - odd–odd:                     `⁅x,y⁆ =  ⁅y,x⁆`
2. **Super Jacobi**:
   - x even: `⁅x,⁅y,z⁆⁆ = ⁅⁅x,y⁆,z⁆ + ⁅y,⁅x,z⁆⁆`
   - x odd, y odd: `⁅x,⁅y,z⁆⁆ = ⁅⁅x,y⁆,z⁆ - ⁅y,⁅x,z⁆⁆`

NOTE: For non-homogeneous x (e.g. even+odd sum), `⁅x,x⁆` may be non-zero.
-/
class SuperLieRing (L : Type*) extends SuperBracket L where
  evenPart : Submodule ℝ L
  oddPart : Submodule ℝ L
  sup_even_odd : evenPart ⊔ oddPart = ⊤
  even_odd_inter : evenPart ⊓ oddPart = ⊥

  -- Graded anti-commutativity for homogeneous x, y
  even_even_skew : ∀ (x y : L), x ∈ evenPart → y ∈ evenPart → bracket x y = -bracket y x
  even_odd_skew  : ∀ (x y : L), x ∈ evenPart → y ∈ oddPart  → bracket x y = -bracket y x
  odd_odd_symm   : ∀ (x y : L), x ∈ oddPart  → y ∈ oddPart  → bracket x y = bracket y x

  -- Super Jacobi on homogeneous generators
  jacobi_even : ∀ (x y z : L), x ∈ evenPart →
    bracket x (bracket y z) = bracket (bracket x y) z + bracket y (bracket x z)

  jacobi_odd_odd : ∀ (x y z : L), x ∈ oddPart → y ∈ oddPart →
    bracket x (bracket y z) = bracket (bracket x y) z - bracket y (bracket x z)

namespace SuperLieRing

variable {L : Type*} [SuperLieRing L]

open SuperBracket

/-- Every element splits into even + odd parts. -/
theorem exists_decomposition (x : L) :
    ∃ (e : L) (o : L), e ∈ evenPart ∧ o ∈ oddPart ∧ x = e + o := by
  have htop : x ∈ (⊤ : Submodule ℝ L) := Submodule.mem_top
  rw [← sup_even_odd] at htop
  rcases Submodule.mem_sup.mp htop with ⟨e, he, o, ho, hx⟩
  exact ⟨e, o, he, ho, hx.symm⟩

/-- Derived: odd-even skew follows from even-odd skew. -/
theorem odd_even_skew (x y : L) (hx : x ∈ oddPart) (hy : y ∈ evenPart) :
    bracket x y = -bracket y x := by
  have h := even_odd_skew y x hy hx
  calc
    bracket x y = -(-bracket x y) := by simp
    _ = -(bracket y x) := by rw [← h]
    _ = -bracket y x := rfl

end SuperLieRing

end InfoGeometry.Algebra

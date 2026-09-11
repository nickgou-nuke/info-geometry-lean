import InfoGeometry.Combinatorics.ExtendedBinaryGolay
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Construction A of the extended binary Golay code

For a binary linear code `C ≤ 𝔽₂ⁿ`, Construction A is the integral lattice

`{x : ℤⁿ | x mod 2 ∈ C}`.

This file constructs that additive lattice for the extended binary Golay code.
It deliberately does not identify it with the Leech lattice: the ordinary
Construction-A lattice has roots, and obtaining the Leech lattice requires the
additional neighbor/congruence construction.
-/

namespace InfoGeometry.Combinatorics.GolayConstructionA

open InfoGeometry.Combinatorics.ExtendedBinaryGolay

abbrev IntegerWord24 := Fin 24 → ℤ

/-- Coordinatewise reduction of an integral word modulo two. -/
def reduceModTwo : IntegerWord24 →+ Word24 where
  toFun := fun x i => (x i : F₂)
  map_zero' := by
    funext i
    simp
  map_add' := by
    intro x y
    funext i
    simp

/--
The integral Construction-A lattice attached to the extended binary Golay
code, represented by its native additive subgroup of `ℤ²⁴`.
-/
def lattice : AddSubgroup IntegerWord24 :=
  codeSubmodule.toAddSubgroup.comap reduceModTwo

@[simp]
theorem mem_lattice_iff (x : IntegerWord24) :
    x ∈ lattice ↔ reduceModTwo x ∈ codeSubmodule :=
  Iff.rfl

/-- Membership can equivalently be read against the finite encoded code. -/
theorem mem_lattice_iff_reduction_mem_code (x : IntegerWord24) :
    x ∈ lattice ↔ reduceModTwo x ∈ code := by
  rw [mem_lattice_iff, ← mem_code_iff_mem_codeSubmodule]

/-- Every vector with all coordinates divisible by two belongs to Construction A. -/
theorem two_smul_mem (x : IntegerWord24) :
    2 • x ∈ lattice := by
  rw [mem_lattice_iff]
  have hzero : reduceModTwo (2 • x) = 0 := by
    funext i
    change ((2 • x) i : F₂) = 0
    rw [two_nsmul, Pi.add_apply]
    calc
      _ = (x i : F₂) + (x i : F₂) :=
        (Int.castRingHom F₂).map_add (x i) (x i)
      _ = 0 := by
        rw [← two_mul]
        change (2 : F₂) * (x i : F₂) = 0
        rw [show (2 : F₂) = 0 by exact CharP.cast_eq_zero F₂ 2, zero_mul]
  rw [hzero]
  exact codeSubmodule.zero_mem

/-- Construction A is closed under addition by its native subgroup owner. -/
theorem add_mem {x y : IntegerWord24}
    (hx : x ∈ lattice) (hy : y ∈ lattice) :
    x + y ∈ lattice :=
  lattice.add_mem hx hy

/-- Construction A is closed under additive inverses. -/
theorem neg_mem {x : IntegerWord24} (hx : x ∈ lattice) :
    -x ∈ lattice :=
  lattice.neg_mem hx

/-- Integral squared-length numerator before the conventional `1 / √2` scaling. -/
def normSqNumerator (x : IntegerWord24) : ℤ :=
  ∑ i, x i * x i

/-- The zero lattice vector has zero squared-length numerator. -/
@[simp]
theorem normSqNumerator_zero :
    normSqNumerator 0 = 0 := by
  simp [normSqNumerator]

/-- Negation preserves the integral squared-length numerator. -/
theorem normSqNumerator_neg (x : IntegerWord24) :
    normSqNumerator (-x) = normSqNumerator x := by
  simp [normSqNumerator]

end InfoGeometry.Combinatorics.GolayConstructionA

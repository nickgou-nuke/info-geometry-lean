import InfoGeometry.Algebra.SupergradedJordanLieSplit

/-!
# Homogeneous closure for the Boolean supergrading

This owner is the bridge from parity labels to actual homogeneous
components.  A `BinaryGrading` is only the multiplication-closure datum; it
does not claim a decomposition of every element into homogeneous parts.
-/

namespace InfoGeometry.Algebra.SupergradedHomogeneousClosure

open InfoGeometry.Algebra.SupergradedBracket

variable {R A : Type*} [Field R] [Ring A] [Algebra R A]
  [NeZero (2 : R)]

structure BinaryGrading where
  component : Bool → Submodule R A
  mul_mem : ∀ (p q : Bool) {x y : A},
    x ∈ component p → y ∈ component q →
      x * y ∈ component (Bool.xor p q)

def Homogeneous (G : BinaryGrading (R := R) (A := A)) (p : Bool) :=
  G.component p

theorem product_mem
    (G : BinaryGrading (R := R) (A := A))
    (p q : Bool) {x y : A}
    (hx : x ∈ Homogeneous G p) (hy : y ∈ Homogeneous G q) :
    x * y ∈ Homogeneous G (Bool.xor p q) :=
  G.mul_mem p q hx hy

theorem superBracket_mem
    (G : BinaryGrading (R := R) (A := A))
    (p q : Bool) {x y : A}
    (hx : x ∈ Homogeneous G p) (hy : y ∈ Homogeneous G q) :
    superBracket p q x y ∈ Homogeneous G (Bool.xor p q) := by
  have hxy := G.mul_mem p q hx hy
  have hyx : y * x ∈ Homogeneous G (Bool.xor p q) := by
    have hcomm : Bool.xor q p = Bool.xor p q := by
      cases p <;> cases q <;> rfl
    rw [← hcomm]
    exact G.mul_mem q p hy hx
  by_cases h : p && q
  · simpa [superBracket, h] using
      (G.component (Bool.xor p q)).add_mem hxy hyx
  · simpa [superBracket, h] using
      (G.component (Bool.xor p q)).sub_mem hxy hyx

theorem gradedJordanProduct_mem
    (G : BinaryGrading (R := R) (A := A))
    (p q : Bool) {x y : A}
    (hx : x ∈ Homogeneous G p) (hy : y ∈ Homogeneous G q) :
    gradedJordanProduct (R := R) p q x y ∈
      Homogeneous G (Bool.xor p q) := by
  have hxy := G.mul_mem p q hx hy
  have hyx : y * x ∈ Homogeneous G (Bool.xor p q) := by
    have hcomm : Bool.xor q p = Bool.xor p q := by
      cases p <;> cases q <;> rfl
    rw [← hcomm]
    exact G.mul_mem q p hy hx
  by_cases h : p && q
  · simpa [gradedJordanProduct, gradedSign, h, sub_eq_add_neg] using
      (G.component (Bool.xor p q)).smul_mem (2 : R)⁻¹
        ((G.component (Bool.xor p q)).sub_mem hxy hyx)
  · simpa [gradedJordanProduct, gradedSign, h] using
      (G.component (Bool.xor p q)).smul_mem (2 : R)⁻¹
        ((G.component (Bool.xor p q)).add_mem hxy hyx)

theorem odd_mul_odd_mem_even
    (G : BinaryGrading (R := R) (A := A)) {x y : A}
    (hx : x ∈ Homogeneous G true) (hy : y ∈ Homogeneous G true) :
    x * y ∈ Homogeneous G false := by
  simpa using G.mul_mem true true hx hy

theorem odd_superBracket_mem_even
    (G : BinaryGrading (R := R) (A := A)) {x y : A}
    (hx : x ∈ Homogeneous G true) (hy : y ∈ Homogeneous G true) :
    superBracket true true x y ∈ Homogeneous G false := by
  simpa using superBracket_mem G true true hx hy

theorem odd_gradedJordanProduct_mem_even
    (G : BinaryGrading (R := R) (A := A)) {x y : A}
    (hx : x ∈ Homogeneous G true) (hy : y ∈ Homogeneous G true) :
    gradedJordanProduct (R := R) true true x y ∈ Homogeneous G false := by
  simpa using gradedJordanProduct_mem G true true hx hy

end InfoGeometry.Algebra.SupergradedHomogeneousClosure

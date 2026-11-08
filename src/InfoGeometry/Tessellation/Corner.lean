import InfoGeometry.Tessellation.VolumeTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Tessellation corner sectors

This file gives the minimal algebraic readout of a causal diamond as a corner.

For an idempotent sector `D.P`, an observable belongs to the local corner when
it is supported on both sides by `D.P`.  This is the predicate-level version of
`eAe`; no projection lattice, von Neumann algebra, or cyclic cohomology layer is
introduced here.
-/

namespace InfoGeometry.Tessellation

/-- Membership in the algebraic corner selected by a causal diamond. -/
def IsInCorner {A : Type*} [Semiring A] (D : Diamond A) (x : A) : Prop :=
  D.P * x = x ∧ x * D.P = x

/-- The sector idempotent belongs to its own corner. -/
theorem Diamond.idempotent_mem_corner
    {A : Type*} [Semiring A] (D : Diamond A) :
    IsInCorner D D.P := by
  exact ⟨D.idem, D.idem⟩

/-- Corner membership is stable under addition. -/
theorem IsInCorner.add
    {A : Type*} [Semiring A] {D : Diamond A} {x y : A}
    (hx : IsInCorner D x) (hy : IsInCorner D y) :
    IsInCorner D (x + y) := by
  constructor
  · rw [mul_add, hx.1, hy.1]
  · rw [add_mul, hx.2, hy.2]

/-- Corner membership is stable under multiplication. -/
theorem IsInCorner.mul
    {A : Type*} [Semiring A] {D : Diamond A} {x y : A}
    (hx : IsInCorner D x) (hy : IsInCorner D y) :
    IsInCorner D (x * y) := by
  constructor
  · calc
      D.P * (x * y) = (D.P * x) * y := by rw [mul_assoc]
      _ = x * y := by rw [hx.1]
  · calc
      (x * y) * D.P = x * (y * D.P) := by rw [mul_assoc]
      _ = x * y := by rw [hy.2]

/-- Corner membership is stable under negation. -/
theorem IsInCorner.neg
    {A : Type*} [Ring A] {D : Diamond A} {x : A}
    (hx : IsInCorner D x) :
    IsInCorner D (-x) := by
  constructor
  · rw [mul_neg, hx.1]
  · rw [neg_mul, hx.2]

/-- Corner membership is stable under subtraction. -/
theorem IsInCorner.sub
    {A : Type*} [Ring A] {D : Diamond A} {x y : A}
    (hx : IsInCorner D x) (hy : IsInCorner D y) :
    IsInCorner D (x - y) := by
  simpa [sub_eq_add_neg] using
    IsInCorner.add (D := D) hx (IsInCorner.neg (D := D) hy)

/-- Unit conjugation transports causal diamonds to causal diamonds. -/
def unitConjDiamond {A : Type*} [Semiring A] (g : Aˣ) (D : Diamond A) :
    Diamond A where
  P := unitConjRing g D.P
  idem := unitConj_idempotent g D.idem

/-- Unit conjugation transports corner membership. -/
theorem unitConjRing_mem_corner
    {A : Type*} [Semiring A] (g : Aˣ) {D : Diamond A} {x : A}
    (hx : IsInCorner D x) :
    IsInCorner (unitConjDiamond g D) (unitConjRing g x) := by
  constructor
  · unfold unitConjDiamond unitConjRing
    calc
      ((g : A) * D.P * ((g⁻¹ : Aˣ) : A)) *
          ((g : A) * x * ((g⁻¹ : Aˣ) : A))
          = (g : A) * D.P * (((g⁻¹ : Aˣ) : A) * (g : A)) * x *
              ((g⁻¹ : Aˣ) : A) := by
              simp [mul_assoc]
      _ = (g : A) * (D.P * x) * ((g⁻¹ : Aˣ) : A) := by
              simp [mul_assoc]
      _ = (g : A) * x * ((g⁻¹ : Aˣ) : A) := by
              rw [hx.1]
  · unfold unitConjDiamond unitConjRing
    calc
      ((g : A) * x * ((g⁻¹ : Aˣ) : A)) *
          ((g : A) * D.P * ((g⁻¹ : Aˣ) : A))
          = (g : A) * x * (((g⁻¹ : Aˣ) : A) * (g : A)) * D.P *
              ((g⁻¹ : Aˣ) : A) := by
              simp [mul_assoc]
      _ = (g : A) * (x * D.P) * ((g⁻¹ : Aˣ) : A) := by
              simp [mul_assoc]
      _ = (g : A) * x * ((g⁻¹ : Aˣ) : A) := by
              rw [hx.2]

end InfoGeometry.Tessellation

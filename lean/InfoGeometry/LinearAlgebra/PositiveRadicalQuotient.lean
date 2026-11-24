/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Analysis.InnerProductSpace.Defs

/-!
# Positive forms on the native radical quotient

For a symmetric real bilinear form `B`, the radical is the native submodule
`LinearMap.ker B`, and Mathlib's `LinearMap.liftQ₂` descends the form to the
native quotient module `V ⧸ LinearMap.ker B`. Symmetry is enough for descent;
positive semidefiniteness is needed to identify zero self-pairing with the
radical and to construct the positive definite inner-product core.

The existing `GrandAnomalyOntology.descendSymmetricPairing` works with an
unbundled pairing on a setoid quotient. Here the carrier is a native quotient
module and the descended pairing is a native `LinearMap.BilinForm`.

Quotienting by the radical preserves every self-pairing, including a negative
one. The construction supplies an `InnerProductSpace.Core`; it does not
assert completeness or supply positivity for an arithmetic Weil form.
-/

namespace InfoGeometry.LinearAlgebra.PositiveRadicalQuotient

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The bilinear form induced on the native quotient by its radical. -/
def quotientForm (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) :
    LinearMap.BilinForm ℝ (V ⧸ LinearMap.ker B) :=
  LinearMap.IsRefl.liftQ₂ B (LinearMap.ker B) hB.isRefl le_rfl

/-- Descending a form preserves its value on any two representatives. -/
@[simp]
theorem quotientForm_mk (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) (v w : V) :
    quotientForm B hB (Submodule.Quotient.mk v) (Submodule.Quotient.mk w) = B v w :=
  rfl

/-- Symmetry descends without any positivity assumption. -/
theorem quotientForm_symm (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (x y : V ⧸ LinearMap.ker B) :
    quotientForm B hB x y = quotientForm B hB y x := by
  refine Submodule.Quotient.induction_on _ x fun v => ?_
  refine Submodule.Quotient.induction_on _ y fun w => ?_
  exact hB.eq v w

/-- The descended form is symmetric in Mathlib's bundled predicate. -/
theorem quotientForm_isSymm (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) :
    (quotientForm B hB).IsSymm :=
  ⟨quotientForm_symm B hB⟩

/-- A positive semidefinite form remains positive semidefinite on its quotient. -/
theorem quotientForm_nonneg (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (hPSD : ∀ v, 0 ≤ B v v) (x : V ⧸ LinearMap.ker B) :
    0 ≤ quotientForm B hB x x := by
  refine Submodule.Quotient.induction_on _ x fun v => ?_
  exact hPSD v

/-- Radical descent cannot create positivity: the quotient form is nonnegative
exactly when the original form is nonnegative. -/
theorem quotientForm_nonneg_iff (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) :
    (∀ x : V ⧸ LinearMap.ker B, 0 ≤ quotientForm B hB x x) ↔
      ∀ v : V, 0 ≤ B v v := by
  constructor
  · intro h v
    exact h (Submodule.Quotient.mk v)
  · intro h
    exact quotientForm_nonneg B hB h

/-- For a symmetric positive semidefinite form, zero self-pairing is exactly
the zero class in the native radical quotient. -/
theorem quotientForm_self_eq_zero_iff (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (hPSD : ∀ v, 0 ≤ B v v) (x : V ⧸ LinearMap.ker B) :
    quotientForm B hB x x = 0 ↔ x = 0 := by
  refine Submodule.Quotient.induction_on _ x fun v => ?_
  rw [quotientForm_mk, Submodule.Quotient.mk_eq_zero]
  exact B.apply_apply_same_eq_zero_iff hPSD hB

/-- A vector with negative self-pairing has a nonzero quotient class with the
same negative self-pairing. No positive semidefiniteness is assumed. -/
theorem negative_survives_radical_quotient (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsSymm) (v : V) (hNeg : B v v < 0) :
    (Submodule.Quotient.mk v : V ⧸ LinearMap.ker B) ≠ 0 ∧
      quotientForm B hB (Submodule.Quotient.mk v) (Submodule.Quotient.mk v) < 0 := by
  constructor
  · intro hzero
    have hker : v ∈ LinearMap.ker B := by
      simpa only [Submodule.Quotient.mk_eq_zero] using hzero
    have hv : B v = 0 := LinearMap.mem_ker.mp hker
    have hdiag : B v v = 0 := by rw [hv, LinearMap.zero_apply]
    exact (ne_of_lt hNeg) hdiag
  · exact hNeg

/-- The inner-product core is constructed from the descended form and proved
positivity, rather than supplied as an assumed structure field. -/
@[instance_reducible]
noncomputable def innerProductCore (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (hPSD : ∀ v, 0 ≤ B v v) : InnerProductSpace.Core ℝ (V ⧸ LinearMap.ker B) where
  inner := fun x y => quotientForm B hB x y
  conj_inner_symm x y := by
    simpa using quotientForm_symm B hB y x
  re_inner_nonneg := quotientForm_nonneg B hB hPSD
  add_left x y z := LinearMap.congr_fun ((quotientForm B hB).map_add x y) z
  smul_left x y r := by
    change quotientForm B hB (r • x) y = r * quotientForm B hB x y
    exact LinearMap.congr_fun ((quotientForm B hB).map_smul r x) y
  definite x hx := (quotientForm_self_eq_zero_iff B hB hPSD x).mp hx

/-- The constructed native core uses precisely the original form on representatives. -/
@[simp]
theorem innerProductCore_inner_mk (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (hPSD : ∀ v, 0 ≤ B v v) (v w : V) :
    (innerProductCore B hB hPSD).inner
      (Submodule.Quotient.mk v) (Submodule.Quotient.mk w) = B v w :=
  rfl

section Maps

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Form preservation reflects membership in the radical of the target. -/
theorem radical_comap_le (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ W)
    (f : V →ₗ[ℝ] W) (hcompat : ∀ x y, C (f x) (f y) = B x y) :
    (LinearMap.ker C).comap f ≤ LinearMap.ker B := by
  intro x hx
  have hCx : C (f x) = 0 := LinearMap.mem_ker.mp hx
  apply LinearMap.mem_ker.mpr
  apply LinearMap.ext
  intro y
  rw [← hcompat x y, hCx, LinearMap.zero_apply, LinearMap.zero_apply]

/-- Symmetry and nonnegativity of the target suffice for forward radical stability. -/
theorem radical_map_le_of_nonneg
    (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ W)
    (f : V →ₗ[ℝ] W) (hC : C.IsSymm) (hPSD : ∀ y, 0 ≤ C y y)
    (hcompat : ∀ x y, C (f x) (f y) = B x y) :
    LinearMap.ker B ≤ (LinearMap.ker C).comap f := by
  intro x hx
  change f x ∈ LinearMap.ker C
  apply (C.apply_apply_same_eq_zero_iff hPSD hC).mp
  rw [hcompat x x]
  simpa only [LinearMap.zero_apply] using
    LinearMap.congr_fun (LinearMap.mem_ker.mp hx) x

/-- Native quotient maps preserve the descended forms when radicals map forward. -/
theorem quotientForm_mapQ
    (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ W)
    (hB : B.IsSymm) (hC : C.IsSymm) (f : V →ₗ[ℝ] W)
    (hRad : LinearMap.ker B ≤ (LinearMap.ker C).comap f)
    (hcompat : ∀ x y, C (f x) (f y) = B x y)
    (x y : V ⧸ LinearMap.ker B) :
    quotientForm C hC ((LinearMap.ker B).mapQ (LinearMap.ker C) f hRad x)
      ((LinearMap.ker B).mapQ (LinearMap.ker C) f hRad y) = quotientForm B hB x y := by
  refine Submodule.Quotient.induction_on _ x fun x => ?_
  refine Submodule.Quotient.induction_on _ y fun y => ?_
  exact hcompat x y

/-- Form-preserving radical quotient maps are injective, even if the original map is not. -/
theorem mapQ_injective
    (B : LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ W)
    (f : V →ₗ[ℝ] W) (hRad : LinearMap.ker B ≤ (LinearMap.ker C).comap f)
    (hcompat : ∀ x y, C (f x) (f y) = B x y) :
    Function.Injective ((LinearMap.ker B).mapQ (LinearMap.ker C) f hRad) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.ker_mapQ,
    le_antisymm (radical_comap_le B C f hcompat) hRad, Submodule.mkQ_map_self]

end Maps

end InfoGeometry.LinearAlgebra.PositiveRadicalQuotient

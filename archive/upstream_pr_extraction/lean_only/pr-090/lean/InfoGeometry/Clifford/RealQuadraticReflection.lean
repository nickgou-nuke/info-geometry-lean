import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

namespace InfoGeometry.Clifford

noncomputable instance quadraticIsometryEquivGroup
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) : Group (Q.IsometryEquiv Q) where
  one := QuadraticMap.IsometryEquiv.refl Q
  mul f g := g.trans f
  inv f := f.symm
  one_mul f := by
    apply DFunLike.ext _ _
    intro x
    rfl
  mul_one f := by
    apply DFunLike.ext _ _
    intro x
    rfl
  mul_assoc f g h := by
    apply DFunLike.ext _ _
    intro x
    rfl
  inv_mul_cancel f := by
    apply DFunLike.ext _ _
    intro x
    change f.symm (f x) = x
    exact f.left_inv x

/-!
# Reflections for real quadratic forms

Mathlib exposes the quadratic-form isometry interface, but its generated
reflection theorem is stated for positive-definite inner-product isometries.
This file supplies the elementary anisotropic reflection itself for an
arbitrary real quadratic form.  It does not assert Cartan--Dieudonne
generation.
-/

noncomputable def realQuadraticReflectionLinear
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v : V) (_hv : Q v ≠ 0) : V →ₗ[ℝ] V where
  toFun x := x - (QuadraticMap.polar (⇑Q) x v / Q v) • v
  map_add' x y := by
    rw [QuadraticMap.polar_add_left, add_div]
    module
  map_smul' a x := by
    rw [QuadraticMap.polar_smul_left]
    change a • x -
        (a • QuadraticMap.polar (⇑Q) x v / Q v) • v =
      a • (x - (QuadraticMap.polar (⇑Q) x v / Q v) • v)
    have hscalar :
        a • QuadraticMap.polar (⇑Q) x v / Q v =
          a * (QuadraticMap.polar (⇑Q) x v / Q v) := by
      simp [smul_eq_mul, div_eq_mul_inv, mul_assoc]
    rw [hscalar]
    change a • x -
        (a * (QuadraticMap.polar (⇑Q) x v / Q v)) • v =
      a • (x - (QuadraticMap.polar (⇑Q) x v / Q v) • v)
    module

@[simp] theorem realQuadraticReflectionLinear_apply
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v x : V) (hv : Q v ≠ 0) :
    realQuadraticReflectionLinear Q v hv x =
      x - (QuadraticMap.polar (⇑Q) x v / Q v) • v :=
  rfl

theorem realQuadraticReflectionLinear_involutive
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v : V) (hv : Q v ≠ 0) :
    Function.Involutive (realQuadraticReflectionLinear Q v hv) := by
  intro x
  let p : ℝ := QuadraticMap.polar (⇑Q) x v
  let q : ℝ := Q v
  have hq : q ≠ 0 := hv
  have hp :
      QuadraticMap.polar (⇑Q)
          (realQuadraticReflectionLinear Q v hv x) v =
        p - (p / q) * (2 * q) := by
    rw [realQuadraticReflectionLinear_apply,
      QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_self]
    dsimp [p, q]
    norm_num [smul_eq_mul]
  rw [realQuadraticReflectionLinear_apply, hp]
  dsimp [p, q]
  have hcoef :
      (QuadraticMap.polar (⇑Q) x v -
          QuadraticMap.polar (⇑Q) x v / Q v * (2 * Q v)) / Q v =
        -(QuadraticMap.polar (⇑Q) x v / Q v) := by
    field_simp
    ring
  rw [hcoef]
  module

noncomputable def realQuadraticReflection
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v : V) (hv : Q v ≠ 0) : V ≃ₗ[ℝ] V :=
  LinearEquiv.ofInvolutive (realQuadraticReflectionLinear Q v hv)
    (realQuadraticReflectionLinear_involutive Q v hv)

@[simp] theorem realQuadraticReflection_apply
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v x : V) (hv : Q v ≠ 0) :
    realQuadraticReflection Q v hv x =
      x - (QuadraticMap.polar (⇑Q) x v / Q v) • v :=
  rfl

theorem realQuadraticReflection_apply_self
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v : V) (hv : Q v ≠ 0) :
    realQuadraticReflection Q v hv v = -v := by
  rw [realQuadraticReflection_apply, QuadraticMap.polar_self]
  change v - ((2 : ℕ) • Q v / Q v) • v = -v
  have hscalar : (2 : ℕ) • Q v / Q v = (2 : ℝ) := by
    simp only [two_nsmul, add_div, div_self hv, one_add_one_eq_two]
  rw [hscalar]
  module

noncomputable def realQuadraticReflectionIsometry
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v : V) (hv : Q v ≠ 0) :
    Q.IsometryEquiv Q := by
  refine QuadraticMap.IsometryEquiv.mk
    (realQuadraticReflection Q v hv) ?_
  intro x
  let p : ℝ := QuadraticMap.polar (⇑Q) x v
  let q : ℝ := Q v
  have hq : q ≠ 0 := hv
  change Q (realQuadraticReflectionLinear Q v hv x) = Q x
  rw [realQuadraticReflectionLinear_apply]
  rw [sub_eq_add_neg, QuadraticMap.map_add (⇑Q), QuadraticMap.map_neg,
    QuadraticMap.map_smul]
  rw [show -((QuadraticMap.polar (⇑Q) x v / Q v) • v) =
      (-(QuadraticMap.polar (⇑Q) x v / Q v)) • v by module]
  rw [QuadraticMap.polar_smul_right]
  norm_num [smul_eq_mul]
  field_simp
  ring

theorem realQuadraticReflectionIsometry_mul_self
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v : V) (hv : Q v ≠ 0) :
    realQuadraticReflectionIsometry Q v hv *
        realQuadraticReflectionIsometry Q v hv =
      (1 : Q.IsometryEquiv Q) := by
  apply DFunLike.ext _ _
  intro x
  change realQuadraticReflection Q v hv
      (realQuadraticReflection Q v hv x) = x
  exact realQuadraticReflectionLinear_involutive Q v hv x

noncomputable def realQuadraticReflectionSet
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) : Set (Q.IsometryEquiv Q) :=
  {g | ∃ (v : V) (hv : Q v ≠ 0),
      g = realQuadraticReflectionIsometry Q v hv}

noncomputable def realQuadraticReflectionSubgroup
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) : Subgroup (Q.IsometryEquiv Q) :=
  Subgroup.closure (realQuadraticReflectionSet Q)

theorem realQuadraticReflectionIsometry_mem_subgroup
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (v : V) (hv : Q v ≠ 0) :
    realQuadraticReflectionIsometry Q v hv ∈
      realQuadraticReflectionSubgroup Q := by
  apply Subgroup.subset_closure
  exact ⟨v, hv, rfl⟩

end InfoGeometry.Clifford

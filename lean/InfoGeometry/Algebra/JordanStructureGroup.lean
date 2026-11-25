/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Jordan.Basic
import InfoGeometry.Algebra.BaezF4H3Zorn

/-!
# Generic Structure Group `Str(J)` over Commutative Jordan Algebras

For an associative commutative ring `R` and a commutative Jordan `R`-algebra
`J` (`[IsCommJordan J]`), this module defines:

* the quadratic representation `jordanU x : Module.End R J`, given by
  `y ↦ 2 • (x * (x * y)) - (x * x) * y`;
* the isotopy condition `IsJordanIsotopy g` asserting the existence of a
  companion linear equivalence `g♯` with `U_{g x} = g ∘ U_x ∘ g♯`;
* the native subgroup `StructureGroup R J : Subgroup (J ≃ₗ[R] J)`;
* the inclusion of Jordan automorphisms into `StructureGroup R J` (with
  companion `g♯ = g⁻¹`);
* specialization to `H3Zorn ℝ`, identifying `jordanU` with `H3Zorn.U` via
  `H3ZornJordanQuadraticReconstruction`.
-/

noncomputable section

namespace InfoGeometry.Algebra

section Generic

section JordanUDef

variable {R J : Type*} [CommRing R] [NonUnitalNonAssocCommRing J] [Module R J]
  [SMulCommClass R J J]

/-- The quadratic representation operator `U_x y = 2 • (x * (x * y)) - (x * x) * y`
on an arbitrary commutative linear Jordan algebra. -/
def jordanU (x : J) : Module.End R J where
  toFun y := (2 : R) • (x * (x * y)) - (x * x) * y
  map_add' y z := by
    simp only [mul_add, smul_add]
    abel
  map_smul' r y := by
    simp only [RingHom.id_apply, mul_smul_comm, smul_comm (2 : R) r, smul_sub]

@[simp] theorem jordanU_apply (x y : J) :
    jordanU (R := R) x y = (2 : R) • (x * (x * y)) - (x * x) * y := rfl

/-- A linear equivalence `g : J ≃ₗ[R] J` is a Jordan isotopy if there exists a
companion linear equivalence `gSharp` intertwining the quadratic representation
`U_{g x} = g ∘ U_x ∘ gSharp`. -/
def IsJordanIsotopy (g : J ≃ₗ[R] J) : Prop :=
  ∃ gSharp : J ≃ₗ[R] J, ∀ x : J,
    jordanU (R := R) (g x) =
      g.toLinearMap.comp ((jordanU (R := R) x).comp gSharp.toLinearMap)

end JordanUDef

/-- The structure group `Str(J)` of a commutative Jordan algebra `[IsCommJordan J]`,
defined generically as the subgroup of `GL(J)` consisting of quadratic-representation
isotopies. -/
def StructureGroup (R J : Type*) [CommRing R] [NonUnitalNonAssocCommRing J] [Module R J]
    [SMulCommClass R J J] [IsCommJordan J] : Subgroup (J ≃ₗ[R] J) where
  carrier := {g | IsJordanIsotopy (R := R) g}
  one_mem' := by
    refine ⟨LinearEquiv.refl R J, fun x => ?_⟩
    ext y
    simp
  mul_mem' := by
    rintro g h ⟨gSharp, hg⟩ ⟨hSharp, hh⟩
    refine ⟨hSharp * gSharp, fun x => ?_⟩
    rw [LinearEquiv.mul_apply, hg (h x), hh x]
    ext y
    rfl
  inv_mem' := by
    rintro g ⟨gSharp, hg⟩
    refine ⟨gSharp⁻¹, fun x => ?_⟩
    have hx := hg (g.symm x)
    simp only [LinearEquiv.apply_symm_apply] at hx
    ext y
    have hy := congrArg (fun f : Module.End R J => g.symm (f (gSharp.symm y))) hx
    simpa [LinearEquiv.coe_toLinearMap] using hy.symm

@[simp] theorem mem_StructureGroup_iff {R J : Type*} [CommRing R]
    [NonUnitalNonAssocCommRing J] [Module R J] [SMulCommClass R J J]
    [IsCommJordan J] (g : J ≃ₗ[R] J) :
    g ∈ StructureGroup R J ↔ IsJordanIsotopy (R := R) g := Iff.rfl

theorem mem_StructureGroup_iff_exists_sharp {R J : Type*} [CommRing R]
    [NonUnitalNonAssocCommRing J] [Module R J] [SMulCommClass R J J]
    [IsCommJordan J] (g : J ≃ₗ[R] J) :
    g ∈ StructureGroup R J ↔
      ∃ gSharp : J ≃ₗ[R] J, ∀ x : J,
        jordanU (R := R) (g x) =
          g.toLinearMap.comp ((jordanU (R := R) x).comp gSharp.toLinearMap) :=
  Iff.rfl

/-- Every linear Jordan automorphism lies in the generic structure group
with companion `e⁻¹`. -/
theorem jordanAut_mem_StructureGroup {R J : Type*} [CommRing R]
    [NonUnitalNonAssocCommRing J] [Module R J] [SMulCommClass R J J]
    [IsCommJordan J] (e : J ≃ₗ[R] J)
    (hmul : ∀ x y : J, e (x * y) = e x * e y) :
    e ∈ StructureGroup R J := by
  refine ⟨e⁻¹, fun x => ?_⟩
  ext y
  change (2 : R) • (e x * (e x * y)) - (e x * e x) * y =
    e ((2 : R) • (x * (x * e.symm y)) - (x * x) * e.symm y)
  rw [map_sub, map_smul, hmul, hmul, hmul, hmul]
  rw [LinearEquiv.apply_symm_apply]

end Generic

section SplitAlbert

open H3Zorn

/-- On the verified 27D split Albert algebra `H3Zorn ℝ`, the generic Jordan
quadratic operator `jordanU` agrees with the cubic quadratic operator `H3Zorn.U`. -/
theorem jordanU_eq_h3Zorn_U (X Y : H3Zorn ℝ) :
    jordanU (R := ℝ) X Y = H3Zorn.U X Y := by
  have hL : ∀ A B : H3Zorn ℝ, A * B = (1 / 2 : ℝ) • T A 1 B := fun A B => rfl
  rw [jordanU_apply, H3ZornJordanQuadraticReconstruction X Y]
  rw [hL (X * X) Y, hL X X, hL X (X * Y), hL X Y]
  rw [T_smul_left, T_smul_right, smul_smul, smul_smul]
  norm_num
  module

/-- Operator equality identifying `jordanU X` on `H3Zorn ℝ` with `H3Zorn.U X`. -/
theorem jordanU_h3Zorn_apply (X Y : H3Zorn ℝ) :
    jordanU (R := ℝ) X Y = H3Zorn.U X Y :=
  jordanU_eq_h3Zorn_U X Y

/-- The structure group `Str(H₃(𝕆_s))` instantiated on the full 27D carrier
`H3Zorn ℝ` via `StructureGroup ℝ (H3Zorn ℝ)`. -/
abbrev H3ZornStructureGroup := StructureGroup ℝ (H3Zorn ℝ)

/-- Every split-Albert Jordan automorphism in `H3ZornJordanAut` belongs to
`StructureGroup ℝ (H3Zorn ℝ)`. -/
theorem H3ZornJordanAut.mem_StructureGroup (e : H3ZornJordanAut) :
    H3ZornJordanAut.toLinearEquiv e ∈ StructureGroup ℝ (H3Zorn ℝ) :=
  jordanAut_mem_StructureGroup
    (H3ZornJordanAut.toLinearEquiv e) (H3ZornJordanAut.map_mul e)

end SplitAlbert

end InfoGeometry.Algebra

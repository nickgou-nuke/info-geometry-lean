/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Basic.Real.Basic

/-!
# Intrinsically real twistor incidence

For real spinor modules `S` and `S'`, the incidence plane of an operator
`x : S' →ₗ[ℝ] S` consists of `(x π, π)`. This is a native submodule and a
native projective map, with an explicit inverse to its spinor parametrization.
The second factor is retained; incidence is the kernel of `ω - x π`, not of
`x π`. The construction is algebraic and flat. For two-dimensional spinor
modules it is the split-signature incidence chart; no complexification,
curved twistor bundle, or differential Penrose transform is used here.
-/

noncomputable section

open scoped LinearAlgebra.Projectivization

namespace InfoGeometry.Twistor.RealTwistorIncidence

variable {S S' : Type*} [AddCommGroup S] [Module ℝ S]
  [AddCommGroup S'] [Module ℝ S']

/-- The real spinor pair in the `(ω, π)` convention. -/
abbrev Carrier (S S' : Type*) := S × S'

/-- The incidence parametrization is an actual linear map. -/
def incidenceMap (x : S' →ₗ[ℝ] S) : S' →ₗ[ℝ] Carrier S S' :=
  x.prod LinearMap.id

@[simp] theorem incidenceMap_apply (x : S' →ₗ[ℝ] S) (π : S') :
    incidenceMap x π = (x π, π) := rfl

theorem incidenceMap_injective (x : S' →ₗ[ℝ] S) :
    Function.Injective (incidenceMap x) := by
  intro π ρ h
  exact congrArg Prod.snd h

/-- The native submodule of incident twistors. -/
def incidenceSpace (x : S' →ₗ[ℝ] S) : Submodule ℝ (Carrier S S') :=
  LinearMap.range (incidenceMap x)

@[simp] theorem mem_incidenceSpace (x : S' →ₗ[ℝ] S) (z : Carrier S S') :
    z ∈ incidenceSpace x ↔ z.1 = x z.2 := by
  constructor
  · rintro ⟨π, rfl⟩
    rfl
  · intro h
    exact ⟨z.2, Prod.ext h.symm rfl⟩

/-- The residual acts on both spinor summands. -/
def residual (x : S' →ₗ[ℝ] S) : Carrier S S' →ₗ[ℝ] S :=
  LinearMap.fst ℝ S S' - x.comp (LinearMap.snd ℝ S S')

@[simp] theorem residual_apply (x : S' →ₗ[ℝ] S) (z : Carrier S S') :
    residual x z = z.1 - x z.2 := rfl

theorem incidenceSpace_eq_ker (x : S' →ₗ[ℝ] S) :
    incidenceSpace x = LinearMap.ker (residual x) := by
  ext z
  simp only [mem_incidenceSpace, LinearMap.mem_ker, residual_apply, sub_eq_zero]

/-- This inverse is the second projection, not a choice of representative. -/
def spinorEquivIncidence (x : S' →ₗ[ℝ] S) : S' ≃ₗ[ℝ] incidenceSpace x where
  toFun π := ⟨incidenceMap x π, ⟨π, rfl⟩⟩
  invFun z := z.val.2
  left_inv π := rfl
  right_inv z := by
    apply Subtype.ext
    exact Prod.ext ((mem_incidenceSpace x z.val).mp z.property).symm rfl
  map_add' π ρ := by
    apply Subtype.ext
    exact (incidenceMap x).map_add π ρ
  map_smul' a π := by
    apply Subtype.ext
    exact (incidenceMap x).map_smul a π

/-- Distinct spacetime operators define distinct incidence subspaces. -/
theorem incidenceSpace_injective :
    Function.Injective (incidenceSpace (S := S) (S' := S')) := by
  intro x y h
  ext π
  have hx : incidenceMap x π ∈ incidenceSpace x := ⟨π, rfl⟩
  rw [h] at hx
  exact (mem_incidenceSpace y _).mp hx

/-- Intersections are precisely the incident spinors annihilated by `x-y`. -/
theorem incidenceMap_mem_intersection_iff (x y : S' →ₗ[ℝ] S) (π : S') :
    incidenceMap x π ∈ incidenceSpace x ⊓ incidenceSpace y ↔ (x - y) π = 0 := by
  simp only [Submodule.mem_inf, mem_incidenceSpace, incidenceMap_apply,
    LinearMap.sub_apply, sub_eq_zero, true_and]

/-- A common nonzero twistor exists exactly when the displacement has a
nonzero spinor in its kernel. No determinant or dimension assumption is needed. -/
theorem shared_nonzero_twistor_iff (x y : S' →ₗ[ℝ] S) :
    (∃ z : Carrier S S', z ≠ 0 ∧ z ∈ incidenceSpace x ∧ z ∈ incidenceSpace y) ↔
      ∃ π : S', π ≠ 0 ∧ (x - y) π = 0 := by
  constructor
  · rintro ⟨z, hz, hx, hy⟩
    have hx' := (mem_incidenceSpace x z).mp hx
    have hy' := (mem_incidenceSpace y z).mp hy
    refine ⟨z.2, ?_, ?_⟩
    · intro hπ
      apply hz
      apply Prod.ext
      · simpa [hπ] using hx'
      · exact hπ
    · exact sub_eq_zero.mpr (hx'.symm.trans hy')
  · rintro ⟨π, hπ, hker⟩
    refine ⟨incidenceMap x π, ?_, ⟨π, rfl⟩, ?_⟩
    · intro h
      exact hπ (congrArg Prod.snd h)
    · exact (mem_incidenceSpace y _).mpr (sub_eq_zero.mp hker)

/-- Native projectivization of the injective real incidence map. -/
def projectiveIncidence (x : S' →ₗ[ℝ] S) : ℙ ℝ S' → ℙ ℝ (Carrier S S') :=
  Projectivization.map (incidenceMap x) (incidenceMap_injective x)

theorem projectiveIncidence_injective (x : S' →ₗ[ℝ] S) :
    Function.Injective (projectiveIncidence x) :=
  Projectivization.map_injective (incidenceMap x) (incidenceMap_injective x)

/-- Translations act on the twistor carrier as real linear shears. -/
def translation (d : S' →ₗ[ℝ] S) : Carrier S S' ≃ₗ[ℝ] Carrier S S' where
  toFun z := (z.1 + d z.2, z.2)
  invFun z := (z.1 - d z.2, z.2)
  left_inv z := by simp
  right_inv z := by simp
  map_add' z w := by
    apply Prod.ext
    · simp [map_add, add_add_add_comm]
    · rfl
  map_smul' a z := by
    apply Prod.ext
    · simp [map_smul, smul_add]
    · rfl

@[simp] theorem translation_incidenceMap (d x : S' →ₗ[ℝ] S) (π : S') :
    translation d (incidenceMap x π) = incidenceMap (x + d) π := rfl

/-- Translation covariance holds as equality of native submodules. -/
theorem translation_incidenceSpace (d x : S' →ₗ[ℝ] S) :
    (incidenceSpace x).map (translation d).toLinearMap = incidenceSpace (x + d) := by
  ext z
  constructor
  · rintro ⟨w, ⟨π, rfl⟩, rfl⟩
    exact ⟨π, rfl⟩
  · rintro ⟨π, rfl⟩
    exact ⟨incidenceMap x π, ⟨π, rfl⟩, rfl⟩

end InfoGeometry.Twistor.RealTwistorIncidence

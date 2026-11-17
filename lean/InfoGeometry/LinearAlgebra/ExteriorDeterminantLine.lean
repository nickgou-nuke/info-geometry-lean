/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Exterior determinant lines for two different vector spaces

For `f : V →ₗ[K] W`, the native map `exteriorPower.map n f` has source
`⋀[K]^n V` and target `⋀[K]^n W`. Its image under the inverse of Mathlib's
canonical tensor--Hom equivalence belongs to
`Module.Dual K (⋀[K]^n V) ⊗[K] (⋀[K]^n W)`.

This tensor product is proved to have dimension one when both spaces have
the common dimension `n`. A pair of bases supplies scalar coordinates on
these genuine exterior spaces. The scalar coefficient transforms with the
inverse target frame and the forward source frame, independently.

All results are finite-dimensional algebra over a field. They require no
inner product, adjoint, identification of `V` with `W`, or chosen complex
structure. No family of operators, line bundle, regularized determinant,
connection, or anomaly-cancellation statement is constructed here.
-/

noncomputable section

open scoped TensorProduct

namespace InfoGeometry.LinearAlgebra.ExteriorDeterminantLine

variable (K V W : Type*) [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- The native dual-tensor carrier. It is a line when `n` is the common
dimension of the source and target spaces. -/
abbrev DeterminantLine (n : ℕ) :=
  Module.Dual K (⋀[K]^n V) ⊗[K] (⋀[K]^n W)

variable {K V W}

/-- The canonical tensor representing the actual `n`th exterior map.
Finiteness is needed only for the source of the tensor--Hom equivalence. -/
def determinantTensor [FiniteDimensional K V] (n : ℕ) (f : V →ₗ[K] W) :
    DeterminantLine K V W n :=
  (dualTensorHomEquiv K (⋀[K]^n V) (⋀[K]^n W)).symm
    (exteriorPower.map n f)

@[simp]
theorem dualTensorHom_determinantTensor [FiniteDimensional K V]
    (n : ℕ) (f : V →ₗ[K] W) :
    dualTensorHom K (⋀[K]^n V) (⋀[K]^n W) (determinantTensor n f) =
      exteriorPower.map n f := by
  exact dualTensorHom_dualTensorHomEquiv_symm _

/-- Explicit common dimension is what makes the native tensor carrier a
one-dimensional determinant line. This includes dimension zero. -/
theorem determinantLine_finrank [FiniteDimensional K V] [FiniteDimensional K W]
    (n : ℕ) (hV : Module.finrank K V = n) (hW : Module.finrank K W = n) :
    Module.finrank K (DeterminantLine K V W n) = 1 := by
  change Module.finrank K
    (Module.Dual K (⋀[K]^n V) ⊗[K] (⋀[K]^n W)) = 1
  simp only [Module.finrank_tensorProduct, Subspace.dual_finrank_eq,
    exteriorPower.finrank_eq, hV, hW, Nat.choose_self, mul_one]

section Coordinates

variable {n : ℕ}

/-- A basis determines a coordinate on the actual top exterior power. -/
def exteriorCoordinate (b : Module.Basis (Fin n) K V) :
    (⋀[K]^n V) →ₗ[K] K :=
  exteriorPower.alternatingMapLinearEquiv b.det

@[simp]
theorem exteriorCoordinate_ιMulti (b : Module.Basis (Fin n) K V)
    (v : Fin n → V) :
    exteriorCoordinate b (exteriorPower.ιMulti K n v) = b.det v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det v

@[simp]
theorem exteriorCoordinate_basis (b : Module.Basis (Fin n) K V) :
    exteriorCoordinate b (exteriorPower.ιMulti K n b) = 1 := by
  rw [exteriorCoordinate_ιMulti, Module.Basis.det_self]

theorem exteriorCoordinate_surjective (b : Module.Basis (Fin n) K V) :
    Function.Surjective (exteriorCoordinate b) := by
  intro r
  refine ⟨r • exteriorPower.ιMulti K n b, ?_⟩
  rw [map_smul, exteriorCoordinate_basis, smul_eq_mul, mul_one]

theorem exteriorCoordinate_injective (b : Module.Basis (Fin n) K V) :
    Function.Injective (exteriorCoordinate b) := by
  letI : FiniteDimensional K V := Module.Finite.of_basis b
  have hdim : Module.finrank K (⋀[K]^n V) = Module.finrank K K := by
    rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis b,
      Fintype.card_fin, Nat.choose_self, Module.finrank_self]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2
    (exteriorCoordinate_surjective b)

/-- The frame-dependent trivialization is proved to be an equivalence;
the exterior carrier itself is not replaced by the scalar field. -/
def exteriorCoordinateEquiv (b : Module.Basis (Fin n) K V) :
    (⋀[K]^n V) ≃ₗ[K] K :=
  LinearEquiv.ofBijective (exteriorCoordinate b)
    ⟨exteriorCoordinate_injective b, exteriorCoordinate_surjective b⟩

/-- The scalar coefficient in an independently chosen source and target
frame. The underlying map still has type `V →ₗ[K] W`. -/
def coefficient (b : Module.Basis (Fin n) K V)
    (c : Module.Basis (Fin n) K W) (f : V →ₗ[K] W) : K :=
  c.det (f ∘ b)

theorem coefficient_eq_det_toMatrix (b : Module.Basis (Fin n) K V)
    (c : Module.Basis (Fin n) K W) (f : V →ₗ[K] W) :
    coefficient b c f = (LinearMap.toMatrix b c f).det := by
  rw [coefficient, Module.Basis.det_apply, LinearMap.toMatrix_eq_basisToMatrix]

/-- The full exterior map, including a singular map, transforms the two
top exterior coordinates by its scalar matrix determinant. -/
theorem exteriorCoordinate_comp_map (b : Module.Basis (Fin n) K V)
    (c : Module.Basis (Fin n) K W) (f : V →ₗ[K] W) :
    (exteriorCoordinate c).comp (exteriorPower.map n f) =
      coefficient b c f • exteriorCoordinate b := by
  let a : V [⋀^Fin n]→ₗ[K] K := c.det.compLinearMap f
  have ha := a.eq_smul_basis_det b
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change exteriorCoordinate c
      (exteriorPower.map n f (exteriorPower.ιMulti K n v)) =
    coefficient b c f * exteriorCoordinate b (exteriorPower.ιMulti K n v)
  rw [exteriorPower.map_apply_ιMulti, exteriorCoordinate_ιMulti,
    exteriorCoordinate_ιMulti]
  exact DFunLike.congr_fun ha v

theorem exteriorCoordinate_map (b : Module.Basis (Fin n) K V)
    (c : Module.Basis (Fin n) K W) (f : V →ₗ[K] W) (x : ⋀[K]^n V) :
    exteriorCoordinate c (exteriorPower.map n f x) =
      coefficient b c f * exteriorCoordinate b x :=
  DFunLike.congr_fun (exteriorCoordinate_comp_map b c f) x

/-- Independent frame covariance. The target factor expresses the old
target frame in the new target frame; the source factor expresses the new
source frame in the old source frame. -/
theorem coefficient_change_basis (b b' : Module.Basis (Fin n) K V)
    (c c' : Module.Basis (Fin n) K W) (f : V →ₗ[K] W) :
    coefficient b' c' f = c'.det c * coefficient b c f * b.det b' := by
  have h := congrArg Matrix.det
    (Module.Basis.basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      b' b c' c f)
  rw [Matrix.det_mul, Matrix.det_mul] at h
  simpa only [coefficient_eq_det_toMatrix, Module.Basis.det_apply] using h.symm

/-- A coordinate coefficient is nonzero exactly when the underlying map
between the two spaces is bijective. No source/target identification is used. -/
theorem coefficient_ne_zero_iff_bijective (b : Module.Basis (Fin n) K V)
    (c : Module.Basis (Fin n) K W) (f : V →ₗ[K] W) :
    coefficient b c f ≠ 0 ↔ Function.Bijective f := by
  rw [coefficient_eq_det_toMatrix]
  constructor
  · intro h
    exact (LinearEquiv.ofIsUnitDet (isUnit_iff_ne_zero.mpr h)).bijective
  · intro h
    exact (LinearEquiv.isUnit_det (LinearEquiv.ofBijective f h) b c).ne_zero

/-- The canonical determinant tensor in the frame-induced pure-tensor
generator. This equation relates the native tensor carrier to its scalar
readout, rather than positing a determinant readout channel. -/
theorem determinantTensor_eq_coefficient_smul [FiniteDimensional K V]
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin n) K W)
    (f : V →ₗ[K] W) :
    determinantTensor n f = coefficient b c f •
      ((exteriorCoordinate b) ⊗ₜ[K] (exteriorPower.ιMulti K n c)) := by
  apply (dualTensorHomEquiv K (⋀[K]^n V) (⋀[K]^n W)).injective
  apply LinearMap.ext
  intro x
  simp only [determinantTensor, LinearEquiv.apply_symm_apply, map_smul,
    LinearMap.smul_apply, dualTensorHomEquiv_tmul]
  apply exteriorCoordinate_injective c
  rw [exteriorCoordinate_map b c f, map_smul, map_smul,
    exteriorCoordinate_basis, smul_eq_mul, smul_eq_mul, mul_one]

/-- Vanishing of the native determinant tensor is equivalent to vanishing
of its coefficient in any pair of frames. -/
theorem determinantTensor_eq_zero_iff_coefficient_eq_zero [FiniteDimensional K V]
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin n) K W)
    (f : V →ₗ[K] W) :
    determinantTensor n f = 0 ↔ coefficient b c f = 0 := by
  constructor
  · intro h
    have hmap : exteriorPower.map n f = 0 := by
      rw [← dualTensorHom_determinantTensor, h, map_zero]
    have hcoord := exteriorCoordinate_map b c f (exteriorPower.ιMulti K n b)
    rw [hmap, LinearMap.zero_apply, map_zero, exteriorCoordinate_basis,
      mul_one] at hcoord
    exact hcoord.symm
  · intro h
    rw [determinantTensor_eq_coefficient_smul b c f, h, zero_smul]

end Coordinates

/-- Nonvanishing of the determinant tensor characterizes a bijection when
the two finite-dimensional spaces have the stated common dimension. -/
theorem determinantTensor_ne_zero_iff_bijective
    [FiniteDimensional K V] [FiniteDimensional K W]
    (n : ℕ) (hV : Module.finrank K V = n) (hW : Module.finrank K W = n)
    (f : V →ₗ[K] W) :
    determinantTensor n f ≠ 0 ↔ Function.Bijective f := by
  let b : Module.Basis (Fin n) K V := Module.finBasisOfFinrankEq K V hV
  let c : Module.Basis (Fin n) K W := Module.finBasisOfFinrankEq K W hW
  rw [ne_eq, determinantTensor_eq_zero_iff_coefficient_eq_zero b c f]
  exact coefficient_ne_zero_iff_bijective b c f

/-- At equal finite rank, nonvanishing also characterizes injectivity. -/
theorem determinantTensor_ne_zero_iff_injective
    [FiniteDimensional K V] [FiniteDimensional K W]
    (n : ℕ) (hV : Module.finrank K V = n) (hW : Module.finrank K W = n)
    (f : V →ₗ[K] W) :
    determinantTensor n f ≠ 0 ↔ Function.Injective f := by
  rw [determinantTensor_ne_zero_iff_bijective n hV hW f]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hV.trans hW.symm)).mp h⟩

end InfoGeometry.LinearAlgebra.ExteriorDeterminantLine

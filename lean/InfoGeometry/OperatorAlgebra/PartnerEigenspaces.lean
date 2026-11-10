/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Nonzero spectral pairing of two composable linear maps

For `A : X → Y` and `B : Y → X`, `A` identifies the nonzero eigenspaces of
`BA` and `AB`; its inverse is `μ⁻¹ B`. This works for unequal and infinite
ambient dimensions. The finite-dimensional corollary compares multiplicities.
An unbounded Dirac realization must additionally establish its domains,
adjoint relation, spectral completeness, and heat trace summability.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PartnerEigenspaces

open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

theorem partner_eigenvector {K X Y : Type*} [Ring K]
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (A : X →ₗ[K] Y) (B : Y →ₗ[K] X)
    {μ : K} {x : X} (hx : B (A x) = μ • x) :
    A (B (A x)) = μ • A x := by
  rw [hx, map_smul]

/-- Over a non-commutative `[DivisionRing K]`, the inverse partner map `y ↦ μ⁻¹ • B y`
maps a `μ`-eigenvector of `A ∘ B` to a `μ`-eigenvector of `B ∘ A` because `μ⁻¹ * μ = 1 = μ * μ⁻¹`. -/
theorem partner_inv_eigenvector {K X Y : Type*} [DivisionRing K]
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (A : X →ₗ[K] Y) (B : Y →ₗ[K] X)
    {μ : K} (hμ : μ ≠ 0) {y : Y} (hy : A (B y) = μ • y) :
    B (A (μ⁻¹ • B y)) = μ • (μ⁻¹ • B y) := by
  rw [map_smul, map_smul, hy, map_smul, smul_smul, smul_smul,
    inv_mul_cancel₀ hμ, mul_inv_cancel₀ hμ]

/-- Over a non-commutative `[DivisionRing K]`, `y ↦ μ⁻¹ • B y` is a left inverse to `A`
on any `μ`-eigenvector of `B ∘ A` (`μ ≠ 0`). -/
theorem partner_left_inv {K X Y : Type*} [DivisionRing K]
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (A : X →ₗ[K] Y) (B : Y →ₗ[K] X)
    {μ : K} (hμ : μ ≠ 0) {x : X} (hx : B (A x) = μ • x) :
    μ⁻¹ • B (A x) = x := by
  rw [hx, smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- Over a non-commutative `[DivisionRing K]`, `y ↦ μ⁻¹ • B y` is a right inverse to `A`
on any `μ`-eigenvector of `A ∘ B` (`μ ≠ 0`). -/
theorem partner_right_inv {K X Y : Type*} [DivisionRing K]
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (A : X →ₗ[K] Y) (B : Y →ₗ[K] X)
    {μ : K} (hμ : μ ≠ 0) {y : Y} (hy : A (B y) = μ • y) :
    A (μ⁻¹ • B y) = y := by
  rw [map_smul, hy, smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- Over any `[CommRing K]`, a unit eigenvalue `μ : Kˣ` induces a linear equivalence
between the `μ`-eigenspace of `B ∘ A` and the `μ`-eigenspace of `A ∘ B`. -/
def unitEigenspaceEquiv {K X Y : Type*} [CommRing K]
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    (A : X →ₗ[K] Y) (B : Y →ₗ[K] X) (μ : Kˣ) :
    Module.End.eigenspace (B.comp A) (μ : K) ≃ₗ[K] Module.End.eigenspace (A.comp B) (μ : K) where
  toFun x := ⟨A x, by
    apply Module.End.mem_eigenspace_iff.mpr
    exact partner_eigenvector A B (Module.End.mem_eigenspace_iff.mp x.property)⟩
  invFun y := ⟨(↑μ⁻¹ : K) • B y, by
    apply Module.End.mem_eigenspace_iff.mpr
    have hy : A (B y) = (μ : K) • (y : Y) :=
      Module.End.mem_eigenspace_iff.mp y.property
    simp only [LinearMap.comp_apply, map_smul]
    rw [hy, map_smul, smul_smul, smul_smul, Units.inv_mul, Units.mul_inv]⟩
  left_inv x := by
    apply Subtype.ext
    have hx : B (A x) = (μ : K) • (x : X) :=
      Module.End.mem_eigenspace_iff.mp x.property
    change (↑μ⁻¹ : K) • B (A x) = (x : X)
    rw [hx, smul_smul, Units.inv_mul, one_smul]
  right_inv y := by
    apply Subtype.ext
    have hy : A (B y) = (μ : K) • (y : Y) :=
      Module.End.mem_eigenspace_iff.mp y.property
    change A ((↑μ⁻¹ : K) • B y) = (y : Y)
    rw [map_smul, hy, smul_smul, Units.inv_mul, one_smul]
  map_add' x y := by apply Subtype.ext; exact map_add A (x : X) (y : X)
  map_smul' c x := by apply Subtype.ext; exact map_smul A c (x : X)

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- The actual linear isomorphism, including its inverse on the eigenspaces. -/
def nonzeroEigenspaceEquiv (A : X →ₗ[K] Y) (B : Y →ₗ[K] X)
    (μ : K) (hμ : μ ≠ 0) :
    Module.End.eigenspace (B.comp A) μ ≃ₗ[K] Module.End.eigenspace (A.comp B) μ where
  toFun x := ⟨A x, by
    apply Module.End.mem_eigenspace_iff.mpr
    exact partner_eigenvector A B (Module.End.mem_eigenspace_iff.mp x.property)⟩
  invFun y := ⟨μ⁻¹ • B y, by
    apply Module.End.mem_eigenspace_iff.mpr
    have hy : A (B y) = μ • (y : Y) :=
      Module.End.mem_eigenspace_iff.mp y.property
    simp only [LinearMap.comp_apply, map_smul]
    rw [hy, map_smul, smul_smul, smul_smul]
    congr 1
    exact mul_comm _ _⟩
  left_inv x := by
    apply Subtype.ext
    have hx : B (A x) = μ • (x : X) :=
      Module.End.mem_eigenspace_iff.mp x.property
    change μ⁻¹ • B (A x) = (x : X)
    rw [hx, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  right_inv y := by
    apply Subtype.ext
    have hy : A (B y) = μ • (y : Y) :=
      Module.End.mem_eigenspace_iff.mp y.property
    change A (μ⁻¹ • B y) = (y : Y)
    rw [map_smul, hy, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  map_add' x y := by apply Subtype.ext; exact map_add A (x : X) (y : X)
  map_smul' c x := by apply Subtype.ext; exact map_smul A c (x : X)

theorem nonzero_eigenspace_finrank_eq
    (A : X →ₗ[K] Y) (B : Y →ₗ[K] X) (μ : K) (hμ : μ ≠ 0) :
    Module.finrank K (Module.End.eigenspace (B.comp A) μ) =
      Module.finrank K (Module.End.eigenspace (A.comp B) μ) :=
  (nonzeroEigenspaceEquiv A B μ hμ).finrank_eq

end InfoGeometry.OperatorAlgebra.PartnerEigenspaces

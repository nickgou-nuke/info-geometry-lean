/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.NoncommutativePlaneWaveKernel
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.RepresentationTheory.Basic

/-!
# Finite group Fourier blocks and translation kernels

The existing finite convolution is pushed through the native universal map
`MonoidAlgebra.lift`.  A representation valued in a possibly noncommutative
algebra gives an ordered product of Fourier blocks.  Replacing `ρ g` by
`ρ g⁻¹` reverses that product; the opposite algebra records this distinction.

The matrix kernel `κ (i * j⁻¹)` is characterized by simultaneous right
translation invariance.  Its matrix product is the existing group convolution.
All sums use counting measure on a finite group.  No irreducibility,
Fourier inversion over a complete dual, or compact-group limit is asserted.
-/

noncomputable section

namespace InfoGeometry.Algebra.FiniteGroupFourier

open scoped BigOperators
open InfoGeometry.Algebra.NoncommutativePlaneWaveKernel

section RepresentationTransform

variable {R A G : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable [Group G] [Fintype G]

/-- Evaluate the native group-algebra transform in a representation. -/
def finiteRepresentationTransform (ρ : G →* A) : (G → R) →ₗ[R] A :=
  (MonoidAlgebra.lift R A G ρ).toLinearMap.comp (finitePlaneWaveTransform (R := R))

/-- The universal group-algebra map computes the actual finite Fourier sum. -/
theorem finiteRepresentationTransform_apply (ρ : G →* A) (f : G → R) :
    finiteRepresentationTransform ρ f = ∑ g : G, f g • ρ g := by
  change MonoidAlgebra.lift R A G ρ (finitePlaneWaveTransform f) = _
  rw [finitePlaneWaveTransform_apply, map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  simp [planeWave]

/-- The forward convention preserves the noncommutative convolution order. -/
theorem finiteRepresentationTransform_convolution [DecidableEq G]
    (ρ : G →* A) (f h : G → R) :
    finiteRepresentationTransform ρ (finiteConvolution f h) =
      finiteRepresentationTransform ρ f * finiteRepresentationTransform ρ h := by
  change MonoidAlgebra.lift R A G ρ (finitePlaneWaveTransform (finiteConvolution f h)) = _
  rw [finitePlaneWaveTransform_mul_convolution, map_mul]
  rfl

/-- Inverse arguments form a representation into the opposite algebra. -/
def inverseOppositeRepresentation (ρ : G →* A) : G →* Aᵐᵒᵖ where
  toFun g := MulOpposite.op (ρ g⁻¹)
  map_one' := by simp
  map_mul' g h := by simp [mul_inv_rev, map_mul, MulOpposite.op_mul]

/-- The inverse convention, evaluated through the native opposite algebra. -/
def inverseFiniteRepresentationTransform (ρ : G →* A) (f : G → R) : A :=
  MulOpposite.unop (finiteRepresentationTransform (inverseOppositeRepresentation ρ) f)

theorem inverseFiniteRepresentationTransform_apply (ρ : G →* A) (f : G → R) :
    inverseFiniteRepresentationTransform ρ f = ∑ g : G, f g • ρ g⁻¹ := by
  simp [inverseFiniteRepresentationTransform, finiteRepresentationTransform_apply,
    inverseOppositeRepresentation]

/-- The inverse convention reverses the matrix-product order. -/
theorem inverseFiniteRepresentationTransform_convolution
    [DecidableEq G] (ρ : G →* A) (f h : G → R) :
    inverseFiniteRepresentationTransform ρ (finiteConvolution f h) =
      inverseFiniteRepresentationTransform ρ h *
        inverseFiniteRepresentationTransform ρ f := by
  unfold inverseFiniteRepresentationTransform
  rw [finiteRepresentationTransform_convolution, MulOpposite.unop_mul]

/-- A native `Representation` has the same finite-sum interpretation. -/
theorem representation_asAlgebraHom_fourier
    {V : Type*} [AddCommMonoid V] [Module R V]
    (ρ : Representation R G V) (f : G → R) :
    ρ.asAlgebraHom (finitePlaneWaveTransform f) = ∑ g : G, f g • ρ g := by
  exact finiteRepresentationTransform_apply ρ f

end RepresentationTransform

section MatrixBlocks

variable {G n : Type*} [Group G] [Fintype G] [DecidableEq G]
variable [Fintype n] [DecidableEq n]

/-- Complex matrix Fourier blocks multiply in forward order. -/
theorem matrixFourier_convolution (ρ : G →* Matrix n n ℂ) (f h : G → ℂ) :
    (∑ g : G, finiteConvolution f h g • ρ g) =
      (∑ g : G, f g • ρ g) * (∑ g : G, h g • ρ g) := by
  simpa only [finiteRepresentationTransform_apply] using
    finiteRepresentationTransform_convolution ρ f h

/-- Complex matrix Fourier blocks with inverse arguments multiply in reverse order. -/
theorem inverseMatrixFourier_convolution (ρ : G →* Matrix n n ℂ) (f h : G → ℂ) :
    (∑ g : G, finiteConvolution f h g • ρ g⁻¹) =
      (∑ g : G, h g • ρ g⁻¹) * (∑ g : G, f g • ρ g⁻¹) := by
  simpa only [inverseFiniteRepresentationTransform_apply] using
    inverseFiniteRepresentationTransform_convolution ρ f h

omit [Fintype G] [DecidableEq G] in
/-- Matrix traces of a representation are scalar and conjugacy invariant. -/
theorem representation_trace_conjugate (ρ : G →* Matrix n n ℂ) (a g : G) :
    Matrix.trace (ρ (a * g * a⁻¹)) = Matrix.trace (ρ g) := by
  simp only [map_mul]
  rw [Matrix.trace_mul_cycle]
  rw [← map_mul, inv_mul_cancel, map_one, one_mul]

end MatrixBlocks

section DifferenceKernel

variable {R G : Type*} [Group G]

/-- The full group-difference matrix, before any choice of Fourier coordinates. -/
def groupDifferenceMatrix (κ : G → R) : Matrix G G R :=
  fun i j => κ (i * j⁻¹)

theorem groupDifferenceMatrix_right_translate (κ : G → R) (i j a : G) :
    groupDifferenceMatrix κ (i * a) (j * a) = groupDifferenceMatrix κ i j := by
  simp [groupDifferenceMatrix, mul_inv_rev, mul_assoc]

theorem groupDifferenceMatrix_first_column (κ : G → R) (i : G) :
    groupDifferenceMatrix κ i 1 = κ i := by
  simp [groupDifferenceMatrix]

/-- The first column uniquely recovers a right-translation invariant matrix. -/
theorem groupDifferenceMatrix_reconstruction (K : Matrix G G R)
    (hK : ∀ i j a : G, K (i * a) (j * a) = K i j) :
    groupDifferenceMatrix (fun i => K i 1) = K := by
  ext i j
  simpa [groupDifferenceMatrix] using hK i j j⁻¹

theorem right_translation_invariant_iff (K : Matrix G G R) :
    (∀ i j a : G, K (i * a) (j * a) = K i j) ↔
      ∃ κ : G → R, K = groupDifferenceMatrix κ := by
  constructor
  · intro hK
    exact ⟨fun i => K i 1, (groupDifferenceMatrix_reconstruction K hK).symm⟩
  · rintro ⟨κ, rfl⟩
    exact groupDifferenceMatrix_right_translate κ

theorem groupDifferenceMatrix_injective :
    Function.Injective (groupDifferenceMatrix : (G → R) → Matrix G G R) := by
  intro κ η h
  funext i
  have hi := congrArg (fun K : Matrix G G R => K i 1) h
  simpa only [groupDifferenceMatrix_first_column] using hi

variable [Semiring R] [Fintype G]

/-- Full matrix multiplication is the existing ordered finite convolution. -/
theorem groupDifferenceMatrix_convolution (f h : G → R) :
    groupDifferenceMatrix (finiteConvolution f h) =
      groupDifferenceMatrix f * groupDifferenceMatrix h := by
  ext i j
  simp only [groupDifferenceMatrix, Matrix.mul_apply, finiteConvolution]
  rw [← (Equiv.inv G |>.trans (Equiv.mulRight i)).sum_comp
    (fun k => f (i * k⁻¹) * h (k * j⁻¹))]
  simp [mul_inv_rev, mul_assoc]

/-- Applying the difference matrix computes convolution on a coefficient vector. -/
theorem groupDifferenceMatrix_mulVec (κ v : G → R) :
    (groupDifferenceMatrix κ).mulVec v = finiteConvolution κ v := by
  funext i
  simp only [Matrix.mulVec_apply_eq_sum, groupDifferenceMatrix, finiteConvolution]
  rw [← (Equiv.inv G |>.trans (Equiv.mulRight i)).sum_comp
    (fun k => κ (i * k⁻¹) * v k)]
  simp [mul_inv_rev]

/-- Convolution commutes with the actual right-translation operator. -/
theorem finiteConvolution_right_translate (κ v : G → R) (a i : G) :
    finiteConvolution κ (fun j => v (j * a)) i =
      finiteConvolution κ v (i * a) := by
  simp only [finiteConvolution, mul_assoc]

/-- The full matrix operator intertwines right translations. -/
theorem groupDifferenceMatrix_mulVec_right_translate (κ v : G → R) (a i : G) :
    (groupDifferenceMatrix κ).mulVec (fun j => v (j * a)) i =
      (groupDifferenceMatrix κ).mulVec v (i * a) := by
  simp only [groupDifferenceMatrix_mulVec, finiteConvolution_right_translate]

end DifferenceKernel

end InfoGeometry.Algebra.FiniteGroupFourier

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitOctonionAutomorphismCore
import InfoGeometry.Algebra.ZornNullIncidence
import InfoGeometry.Lie.CanonicalZornRegularDerivation
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Automorphism covariance of split-octonion null-plane incidence

The acting group is the existing subgroup of real linear equivalences that
preserve the actual Zorn multiplication and unit. Its action carries the
kernel of `L_x` linearly onto the kernel of `L_(φ x)`.

These statements concern algebra automorphisms, not arbitrary orthogonal
transformations. They neither add a smooth gauge connection nor identify the
full orthogonal group with multiplication-preserving automorphisms.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionNullPlaneCovariance

open InfoGeometry.Canonical
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge

/-- Restriction of the existing canonical/vector coordinate equivalence to
the two kernels. The product-preservation theorem supplies the incidence
compatibility; no new multiplication is introduced. -/
def canonicalVectorLeftKernelEquiv (x : SplitOctonionReal) :
    LinearMap.ker (leftMultiplication x) ≃ₗ[ℝ]
      LinearMap.ker
        (InfoGeometry.Algebra.ZornLeftCAR.leftMultiplication (canonicalVectorEquiv x)) where
  toFun y := ⟨canonicalVectorEquiv y, by
    change InfoGeometry.Algebra.ZornVectorMatrix.mul
      (canonicalVectorEquiv x) (canonicalVectorEquiv y) = 0
    rw [← canonicalVectorEquiv_mul]
    have hy : x * (y : SplitOctonionReal) = 0 := y.property
    exact (congrArg canonicalVectorEquiv hy).trans canonicalVectorEquiv_zero⟩
  invFun y := ⟨canonicalVectorEquiv.symm y, by
    change x * canonicalVectorEquiv.symm y = 0
    apply canonicalVectorEquiv.injective
    rw [canonicalVectorEquiv_mul, Equiv.apply_symm_apply, canonicalVectorEquiv_zero]
    exact y.property⟩
  left_inv y := by
    apply Subtype.ext
    exact canonicalVectorEquiv.symm_apply_apply y
  right_inv y := by
    apply Subtype.ext
    exact canonicalVectorEquiv.apply_symm_apply y
  map_add' y z := by
    apply Subtype.ext
    exact canonicalVectorEquiv_add y z
  map_smul' r y := by
    apply Subtype.ext
    exact canonicalVectorEquiv_smul r y

/-- The nonzero-null dimension-four theorem on the same canonical carrier
used by the genuine automorphism action. -/
theorem canonical_leftKernel_finrank {x : SplitOctonionReal} (hx : x ≠ 0)
    (hn : ZornMatrix.detZ x = 0) :
    Module.finrank ℝ (LinearMap.ker (leftMultiplication x)) = 4 := by
  rw [(canonicalVectorLeftKernelEquiv x).finrank_eq]
  apply InfoGeometry.Algebra.ZornNullIncidence.leftKernel_finrank
  · intro hzero
    apply hx
    apply canonicalVectorEquiv.injective
    simpa only [canonicalVectorEquiv_zero] using hzero
  · simpa [InfoGeometry.Algebra.ZornVectorMatrix.norm,
      canonicalVectorEquiv, ZornMatrix.detZ, ZornMatrix.dot,
      InfoGeometry.Algebra.ZornVec3.dot, Fin.sum_univ_three] using hn

/-- Zero-product incidence is invariant under the genuine algebra automorphism
group. -/
theorem automorphism_mem_leftKernel_iff (φ : RealSplitOctonionAut)
    (x y : SplitOctonionReal) :
    (φ : SplitOctonionAutCandidate ℝ) y ∈
        LinearMap.ker (leftMultiplication ((φ : SplitOctonionAutCandidate ℝ) x)) ↔
      y ∈ LinearMap.ker (leftMultiplication x) := by
  change (φ : SplitOctonionAutCandidate ℝ) x *
      (φ : SplitOctonionAutCandidate ℝ) y = 0 ↔ x * y = 0
  rw [← RealSplitOctonionAut.preserves_mul]
  exact (φ : SplitOctonionAutCandidate ℝ).map_eq_zero_iff

/-- The automorphism restricts to an explicit linear equivalence of the two
annihilator planes. -/
def leftKernelAut (φ : RealSplitOctonionAut) (x : SplitOctonionReal) :
    LinearMap.ker (leftMultiplication x) ≃ₗ[ℝ]
      LinearMap.ker (leftMultiplication ((φ : SplitOctonionAutCandidate ℝ) x)) where
  toFun y := ⟨(φ : SplitOctonionAutCandidate ℝ) y,
    (automorphism_mem_leftKernel_iff φ x y).mpr y.property⟩
  invFun y := ⟨(φ : SplitOctonionAutCandidate ℝ).symm y, by
    apply (automorphism_mem_leftKernel_iff φ x
      ((φ : SplitOctonionAutCandidate ℝ).symm y)).mp
    simpa only [LinearEquiv.apply_symm_apply] using y.property⟩
  left_inv y := by
    apply Subtype.ext
    exact (φ : SplitOctonionAutCandidate ℝ).symm_apply_apply y
  right_inv y := by
    apply Subtype.ext
    exact (φ : SplitOctonionAutCandidate ℝ).apply_symm_apply y
  map_add' y z := by
    apply Subtype.ext
    exact map_add (φ : SplitOctonionAutCandidate ℝ) y z
  map_smul' r y := by
    apply Subtype.ext
    exact map_smul (φ : SplitOctonionAutCandidate ℝ) r y

/-- The kernel assignment is equivariant as an equality of native submodules. -/
theorem automorphism_map_leftKernel (φ : RealSplitOctonionAut)
    (x : SplitOctonionReal) :
    (LinearMap.ker (leftMultiplication x)).map
        (φ : SplitOctonionAutCandidate ℝ).toLinearMap =
      LinearMap.ker (leftMultiplication ((φ : SplitOctonionAutCandidate ℝ) x)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (automorphism_mem_leftKernel_iff φ x z).mpr hz
  · intro hy
    refine ⟨(φ : SplitOctonionAutCandidate ℝ).symm y, ?_,
      (φ : SplitOctonionAutCandidate ℝ).apply_symm_apply y⟩
    apply (automorphism_mem_leftKernel_iff φ x
      ((φ : SplitOctonionAutCandidate ℝ).symm y)).mp
    simpa only [LinearEquiv.apply_symm_apply] using hy

/-- Kernel dimension is an invariant of the multiplication automorphism
action. -/
theorem automorphism_leftKernel_finrank (φ : RealSplitOctonionAut)
    (x : SplitOctonionReal) :
    Module.finrank ℝ
        (LinearMap.ker (leftMultiplication ((φ : SplitOctonionAutCandidate ℝ) x))) =
      Module.finrank ℝ (LinearMap.ker (leftMultiplication x)) :=
  (leftKernelAut φ x).finrank_eq.symm

/-- Multiplication has identical structure constants in a basis and its
image under an algebra automorphism. Both the inputs and coordinate frame
are transported; an arbitrary orthogonal frame change is not asserted to
preserve the product. -/
theorem automorphism_structureConstants {ι : Type*}
    (b : Module.Basis ι ℝ SplitOctonionReal) (φ : RealSplitOctonionAut)
    (i j k : ι) :
    (b.map (φ : SplitOctonionAutCandidate ℝ)).repr
        ((b.map (φ : SplitOctonionAutCandidate ℝ)) i *
          (b.map (φ : SplitOctonionAutCandidate ℝ)) j) k =
      b.repr (b i * b j) k := by
  change b.repr ((φ : SplitOctonionAutCandidate ℝ).symm
      ((φ : SplitOctonionAutCandidate ℝ) (b i) *
        (φ : SplitOctonionAutCandidate ℝ) (b j))) k = _
  rw [← RealSplitOctonionAut.preserves_mul, LinearEquiv.symm_apply_apply]

/-- A derivation differentiates the exact zero-product incidence relation.
This is the infinitesimal algebraic covariance identity, with both moving
arguments retained. -/
theorem derivation_zeroProduct
    (D : Module.End ℝ SplitOctonionReal)
    (hD : InfoGeometry.Lie.CanonicalZornDerivation.IsDerivation D)
    {x y : SplitOctonionReal} (hxy : x * y = 0) :
    D x * y + x * D y = 0 := by
  rw [← hD x y, hxy, map_zero]

/-- A derivation stabilizing the acting element preserves its left-action
kernel. Without `D x = 0`, only the two-argument identity above is asserted. -/
theorem derivation_preserves_leftKernel
    (D : Module.End ℝ SplitOctonionReal)
    (hD : InfoGeometry.Lie.CanonicalZornDerivation.IsDerivation D)
    {x : SplitOctonionReal} (hx : D x = 0) :
    Set.MapsTo D (LinearMap.ker (leftMultiplication x))
      (LinearMap.ker (leftMultiplication x)) := by
  intro y hy
  change x * D y = 0
  have hxy : x * y = 0 := hy
  have h := derivation_zeroProduct D hD hxy
  rw [hx, InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.zero_mul,
    zero_add] at h
  exact h

end InfoGeometry.Lie.SplitOctonionNullPlaneCovariance

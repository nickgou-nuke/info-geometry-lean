/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.RealPositiveOperatorGap
import InfoGeometry.Canonical.RealLieJordanGeometry

/-!
# Two real operator gaps on their respective carriers

The matrix Gram sum acts on Euclidean vectors. The negative symmetric
Lie--Jordan generator acts on the full matrix algebra with its native
Frobenius inner product. Each has a positive coercivity constant away from
its entire kernel. The constants belong to fixed finite operators; no
uniform family bound or field-theory interpretation is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealLieJordanGap

open scoped InnerProductSpace Matrix
open Core.LieJordanGenerators Analysis.RealPositiveOperatorGap
open RealLieJordanGeometry

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

section VectorOperator

/-- The Gram sum is positive as an operator on the native Euclidean space. -/
theorem gram_toEuclideanLin_isPositive (u : Matrix n n ℝ) :
    (u * uᵀ + uᵀ * u).toEuclideanLin.IsPositive := by
  apply Matrix.isPositive_toEuclideanLin_iff.mpr
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_self_mul_conjTranspose u).add
      (Matrix.posSemidef_conjTranspose_mul_self u)

/-- The matrix-to-vector map preserves the two ordered Gram products. -/
theorem gram_toEuclideanLin (u : Matrix n n ℝ) :
    (u * uᵀ + uᵀ * u).toEuclideanLin =
      u.toEuclideanLin * uᵀ.toEuclideanLin +
        uᵀ.toEuclideanLin * u.toEuclideanLin := by
  change Matrix.toLpLin 2 2 (u * uᵀ + uᵀ * u) = _
  simp only [map_add, Matrix.toLpLin_mul_same]
  rfl

/-- The vector kernel is the simultaneous kernel of the matrix and its transpose. -/
theorem ker_gram_toEuclideanLin (u : Matrix n n ℝ) :
    (u * uᵀ + uᵀ * u).toEuclideanLin.ker =
      u.toEuclideanLin.ker ⊓ uᵀ.toEuclideanLin.ker := by
  have hadj : uᵀ.toEuclideanLin = u.toEuclideanLin.adjoint := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint u
  rw [gram_toEuclideanLin]
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_inf]
  apply HodgeCohomology.HodgeDirac.harmonic_iff_closed_and_coclosed
  intro a b
  rw [hadj]
  exact (u.toEuclideanLin.adjoint_inner_right a b).symm

/-- A vector-space coercivity bound and the matrix-algebra spectrum use the same constant. -/
theorem gram_exists_positive_bound_and_spectral_gap (u : Matrix n n ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ x ∈ (u.toEuclideanLin.ker ⊓ uᵀ.toEuclideanLin.ker)ᗮ,
        δ * ‖x‖ ^ 2 ≤ inner ℝ x ((u * uᵀ + uᵀ * u).toEuclideanLin x)) ∧
      ∀ μ ∈ spectrum ℝ (u * uᵀ + uᵀ * u), μ = 0 ∨ δ ≤ μ := by
  have hpos := gram_toEuclideanLin_isPositive u
  obtain ⟨δ, hδ, hbound⟩ := exists_positive_coercive_bound _ hpos
  refine ⟨δ, hδ, ?_, fun μ hμ => ?_⟩
  · simpa only [ker_gram_toEuclideanLin] using hbound
  · have hspectrum : μ ∈ spectrum ℝ (u * uᵀ + uᵀ * u).toEuclideanLin := by
      change μ ∈ spectrum ℝ
        ((Matrix.toLpLinAlgEquiv (R := ℝ) (n := n) 2) (u * uᵀ + uᵀ * u))
      rwa [AlgEquiv.spectrum_eq]
    exact spectrum_gap_of_coercive_bound _ hpos.isSymmetric hbound hspectrum

end VectorOperator

section MatrixOperator

open scoped InfoGeometry.Canonical.RealLieJordanGeometry

/-- The full matrix kernel remains the native common centralizer after changing sign. -/
theorem ker_neg_symmetricGenerator (u : Matrix n n ℝ) :
    (-symmetricGenerator (R := ℝ) u uᵀ).ker =
      (Subalgebra.centralizer ℝ ({u, uᵀ} : Set (Matrix n n ℝ))).toSubmodule := by
  rw [LinearMap.ker_neg, ker_symmetricGenerator_eq_centralizer]

/-- A coercive bound on the entire centralizer complement excludes small nonzero spectrum. -/
theorem generator_exists_positive_bound_and_spectral_gap (u : Matrix n n ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ x ∈ (Subalgebra.centralizer ℝ
          ({u, uᵀ} : Set (Matrix n n ℝ))).toSubmoduleᗮ,
        δ * ‖x‖ ^ 2 ≤ inner ℝ x ((-symmetricGenerator (R := ℝ) u uᵀ) x)) ∧
      ∀ μ ∈ spectrum ℝ (-symmetricGenerator (R := ℝ) u uᵀ), μ = 0 ∨ δ ≤ μ := by
  have hpos := neg_symmetricGenerator_isPositive u
  obtain ⟨δ, hδ, hbound⟩ := exists_positive_coercive_bound _ hpos
  refine ⟨δ, hδ, ?_, fun _ hμ => ?_⟩
  · simpa only [ker_neg_symmetricGenerator] using hbound
  · exact spectrum_gap_of_coercive_bound _ hpos.isSymmetric hbound hμ

end MatrixOperator

end InfoGeometry.Canonical.RealLieJordanGap

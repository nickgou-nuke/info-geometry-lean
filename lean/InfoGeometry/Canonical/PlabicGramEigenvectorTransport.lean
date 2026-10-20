/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Canonical.FinitePlabicKasteleyn

/-!
# Eigenvector transport between the two finite Gram operators

For a complex rectangular matrix, multiplication by the matrix transports a
nonzero-eigenvalue eigenvector of `Aᴴ A` to one of `A Aᴴ`.  This is the
vector-level finite statement; it does not assert equality of characteristic
polynomials, multiplicities, or a singular-value decomposition.
-/

namespace InfoGeometry.Canonical.PlabicGramEigenvectorTransport

open InfoGeometry.Canonical.FinitePlabicKasteleyn

/-- Applying a rectangular matrix transports an eigenvector of
`A.conjTranspose * A` to one of `A * A.conjTranspose` with the same eigenvalue. -/
theorem mulVec_gram_eigenvector {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (eigenvalue : ℂ) (v : n → ℂ)
    (h : (A.conjTranspose * A).mulVec v = eigenvalue • v) :
    (A * A.conjTranspose).mulVec (A.mulVec v) = eigenvalue • (A.mulVec v) := by
  calc
    (A * A.conjTranspose).mulVec (A.mulVec v) =
        A.mulVec (A.conjTranspose.mulVec (A.mulVec v)) := by
          simp only [Matrix.mulVec_mulVec]
          rw [Matrix.mul_assoc]
    _ = A.mulVec ((A.conjTranspose * A).mulVec v) := by
          rw [← Matrix.mulVec_mulVec]
    _ = A.mulVec (eigenvalue • v) := by rw [h]
    _ = eigenvalue • (A.mulVec v) := by rw [Matrix.mulVec_smul]

/-- If the eigenvalue is nonzero, transport by `A` cannot annihilate a
nonzero eigenvector of `A.conjTranspose * A`. -/
theorem mulVec_gram_eigenvector_ne_zero {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (eigenvalue : ℂ) (v : n → ℂ)
    (hEigenvalue_ne_zero : eigenvalue ≠ 0) (hv : v ≠ 0)
    (h : (A.conjTranspose * A).mulVec v = eigenvalue • v) :
    A.mulVec v ≠ 0 := by
  intro hAv
  apply hv
  have hzero : (0 : n → ℂ) = eigenvalue • v := by
    calc
      (0 : n → ℂ) = A.conjTranspose.mulVec (A.mulVec v) := by rw [hAv]; simp
      _ = (A.conjTranspose * A).mulVec v := by rw [Matrix.mulVec_mulVec]
      _ = eigenvalue • v := h
  rcases (smul_eq_zero.mp hzero.symm) with heigenvalue | hv'
  · exact (hEigenvalue_ne_zero heigenvalue).elim
  · exact hv'

/-- For a nonzero eigenvalue, the Gram-eigenvector transport is injective on
the corresponding eigenspace. -/
theorem mulVec_gram_eigenvector_injective {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (eigenvalue : ℂ) (hEigenvalue_ne_zero : eigenvalue ≠ 0)
    {v₁ v₂ : n → ℂ}
    (h₁ : (A.conjTranspose * A).mulVec v₁ = eigenvalue • v₁)
    (h₂ : (A.conjTranspose * A).mulVec v₂ = eigenvalue • v₂)
    (hEq : A.mulVec v₁ = A.mulVec v₂) :
    v₁ = v₂ := by
  have hmul : eigenvalue • v₁ = eigenvalue • v₂ := by
    calc
      eigenvalue • v₁ = (A.conjTranspose * A).mulVec v₁ := h₁.symm
      _ = A.conjTranspose.mulVec (A.mulVec v₁) := by
        rw [Matrix.mulVec_mulVec]
      _ = A.conjTranspose.mulVec (A.mulVec v₂) := by rw [hEq]
      _ = (A.conjTranspose * A).mulVec v₂ := by
        rw [Matrix.mulVec_mulVec]
      _ = eigenvalue • v₂ := h₂
  have hdiff : eigenvalue • (v₁ - v₂) = 0 := by
    rw [smul_sub, hmul, sub_self]
  rcases smul_eq_zero.mp hdiff with hzero | hv
  · exact (hEigenvalue_ne_zero hzero).elim
  · exact sub_eq_zero.mp hv

/-- The reverse transport, using `A.conjTranspose`, gives the corresponding
eigenvector statement from `A * A.conjTranspose` back to the other Gram matrix. -/
theorem conjTranspose_mulVec_gram_eigenvector {m n : Type*}
    [Fintype m] [Fintype n] (A : Matrix m n ℂ) (eigenvalue : ℂ) (w : m → ℂ)
    (h : (A * A.conjTranspose).mulVec w = eigenvalue • w) :
    (A.conjTranspose * A).mulVec (A.conjTranspose.mulVec w) =
      eigenvalue • (A.conjTranspose.mulVec w) := by
  have hA :
      ((A.conjTranspose.conjTranspose * A.conjTranspose).mulVec w) =
        eigenvalue • w := by
    simpa only [Matrix.conjTranspose_conjTranspose] using h
  have htransport :=
    mulVec_gram_eigenvector (A := A.conjTranspose) eigenvalue w hA
  simpa only [Matrix.conjTranspose_conjTranspose] using htransport

/-- At a nonzero eigenvalue, every eigenvector of `A * Aᴴ` has a preimage in
the `Aᴴ * A` eigenspace. The preimage is obtained by applying `Aᴴ` and
scaling by the inverse eigenvalue. -/
theorem mulVec_gram_eigenvector_preimage {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (eigenvalue : ℂ) (hEigenvalue_ne_zero : eigenvalue ≠ 0)
    (w : m → ℂ)
    (h : (A * A.conjTranspose).mulVec w = eigenvalue • w) :
    ∃ v : n → ℂ,
      (A.conjTranspose * A).mulVec v = eigenvalue • v ∧ A.mulVec v = w := by
  let v := eigenvalue⁻¹ • A.conjTranspose.mulVec w
  have hEigen := conjTranspose_mulVec_gram_eigenvector A eigenvalue w h
  refine ⟨v, ?_, ?_⟩
  · dsimp [v]
    calc
      (A.conjTranspose * A).mulVec
          (eigenvalue⁻¹ • A.conjTranspose.mulVec w) =
          eigenvalue⁻¹ • (A.conjTranspose * A).mulVec
            (A.conjTranspose.mulVec w) := by rw [Matrix.mulVec_smul]
      _ = eigenvalue⁻¹ • (eigenvalue • A.conjTranspose.mulVec w) := by
        rw [hEigen]
      _ = eigenvalue • (eigenvalue⁻¹ • A.conjTranspose.mulVec w) := by
        simp [smul_smul, mul_comm]
  · dsimp [v]
    have hmul : A.mulVec (A.conjTranspose.mulVec w) = eigenvalue • w := by
      simpa only [Matrix.mulVec_mulVec] using h
    calc
      A.mulVec (eigenvalue⁻¹ • A.conjTranspose.mulVec w) =
          eigenvalue⁻¹ • A.mulVec (A.conjTranspose.mulVec w) := by
        rw [Matrix.mulVec_smul]
      _ = eigenvalue⁻¹ • (eigenvalue • w) := by
        rw [hmul]
      _ = w := by simp [smul_smul, hEigenvalue_ne_zero]

/-- The two Gram operators have eigenspaces of equal finite dimension at every
nonzero eigenvalue. This is geometric multiplicity equality; it makes no
claim about generalized eigenspaces or characteristic polynomials. -/
theorem gram_eigenspace_finrank_eq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) (eigenvalue : ℂ) (hEigenvalue_ne_zero : eigenvalue ≠ 0) :
    Module.finrank ℂ
        (Module.End.eigenspace (A.conjTranspose * A).mulVecLin eigenvalue) =
      Module.finrank ℂ
        (Module.End.eigenspace (A * A.conjTranspose).mulVecLin eigenvalue) := by
  let source := Module.End.eigenspace (A.conjTranspose * A).mulVecLin eigenvalue
  let target := Module.End.eigenspace (A * A.conjTranspose).mulVecLin eigenvalue
  let forward : source →ₗ[ℂ] target :=
    ((A.mulVecLin).comp source.subtype).codRestrict target (by
      intro v
      rw [Module.End.mem_eigenspace_iff]
      exact mulVec_gram_eigenvector A eigenvalue v.1
        (Module.End.mem_eigenspace_iff.mp v.2))
  let backward : target →ₗ[ℂ] source :=
    ((A.conjTranspose.mulVecLin).comp target.subtype).codRestrict source (by
      intro w
      rw [Module.End.mem_eigenspace_iff]
      exact conjTranspose_mulVec_gram_eigenvector A eigenvalue w.1
        (Module.End.mem_eigenspace_iff.mp w.2))
  have hforward : Function.Injective forward := by
    intro v₁ v₂ h
    apply Subtype.ext
    apply mulVec_gram_eigenvector_injective A eigenvalue hEigenvalue_ne_zero
      (Module.End.mem_eigenspace_iff.mp v₁.2)
      (Module.End.mem_eigenspace_iff.mp v₂.2)
    have hval := congrArg Subtype.val h
    simpa [forward] using hval
  have hbackward : Function.Injective backward := by
    intro w₁ w₂ h
    apply Subtype.ext
    apply mulVec_gram_eigenvector_injective A.conjTranspose eigenvalue
      hEigenvalue_ne_zero
      (by simpa only [Matrix.mulVecLin_apply, Matrix.conjTranspose_conjTranspose] using
        Module.End.mem_eigenspace_iff.mp w₁.2)
      (by simpa only [Matrix.mulVecLin_apply, Matrix.conjTranspose_conjTranspose] using
        Module.End.mem_eigenspace_iff.mp w₂.2)
    have hval := congrArg Subtype.val h
    simpa [backward] using hval
  apply le_antisymm
  · exact forward.finrank_le_finrank_of_injective hforward
  · exact backward.finrank_le_finrank_of_injective hbackward

/- The two Gram matrices have identical characteristic polynomials in the
    square case.  The rectangular case only has the nonzero-eigenvalue
    transport and finite-eigenspace result above. -/
theorem gram_charpoly_eq_of_square {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) :
    Matrix.charpoly (A.conjTranspose * A) =
      Matrix.charpoly (A * A.conjTranspose) := by
  exact Matrix.charpoly_mul_comm A.conjTranspose A

/-- The abstract transport theorem applies to the signed Plabic edge-sum
matrix with its owner-prescribed `White × Black` orientation. -/
theorem edgeSumMatrix_mulVec_gram_eigenvector
    {G : FinitePlabicGraph} {R : Type*} [CommRing R] [StarRing R]
    (S : KasteleynSigning G) (weight : G.Edge → ℂ) (eigenvalue : ℂ)
    (v : G.Black → ℂ)
    (h : ((edgeSumMatrix S weight).conjTranspose * edgeSumMatrix S weight).mulVec v =
      eigenvalue • v) :
    ((edgeSumMatrix S weight) * (edgeSumMatrix S weight).conjTranspose).mulVec
        ((edgeSumMatrix S weight).mulVec v) =
      eigenvalue • ((edgeSumMatrix S weight).mulVec v) := by
  exact mulVec_gram_eigenvector (edgeSumMatrix S weight) eigenvalue v h

/-- The nonzero-eigenvalue transport remains non-annihilating for a Plabic
edge-sum matrix. -/
theorem edgeSumMatrix_mulVec_gram_eigenvector_ne_zero
    {G : FinitePlabicGraph} {R : Type*} [CommRing R] [StarRing R]
    (S : KasteleynSigning G) (weight : G.Edge → ℂ) (eigenvalue : ℂ)
    (v : G.Black → ℂ) (hEigenvalue_ne_zero : eigenvalue ≠ 0) (hv : v ≠ 0)
    (h : ((edgeSumMatrix S weight).conjTranspose * edgeSumMatrix S weight).mulVec v =
      eigenvalue • v) :
    (edgeSumMatrix S weight).mulVec v ≠ 0 := by
  exact mulVec_gram_eigenvector_ne_zero (edgeSumMatrix S weight) eigenvalue v
    hEigenvalue_ne_zero hv h

/- The same nonzero-eigenvalue hypothesis gives injectivity on the
   eigenspace for the concrete Plabic edge-sum matrix. -/
theorem edgeSumMatrix_mulVec_gram_eigenvector_injective
    {G : FinitePlabicGraph} {R : Type*} [CommRing R] [StarRing R]
    (S : KasteleynSigning G) (weight : G.Edge → ℂ) (eigenvalue : ℂ)
    (hEigenvalue_ne_zero : eigenvalue ≠ 0)
    {v₁ v₂ : G.Black → ℂ}
    (h₁ : ((edgeSumMatrix S weight).conjTranspose * edgeSumMatrix S weight).mulVec v₁ =
      eigenvalue • v₁)
    (h₂ : ((edgeSumMatrix S weight).conjTranspose * edgeSumMatrix S weight).mulVec v₂ =
      eigenvalue • v₂)
    (hEq : (edgeSumMatrix S weight).mulVec v₁ =
      (edgeSumMatrix S weight).mulVec v₂) :
    v₁ = v₂ := by
  exact mulVec_gram_eigenvector_injective (edgeSumMatrix S weight) eigenvalue
    hEigenvalue_ne_zero h₁ h₂ hEq

/-- The concrete signed Plabic edge-sum matrix has the same geometric
multiplicity on its two Gram blocks at nonzero eigenvalues. -/
theorem edgeSumMatrix_gram_eigenspace_finrank_eq
    {G : FinitePlabicGraph} (S : KasteleynSigning G)
    (weight : G.Edge → ℂ) (eigenvalue : ℂ) (hEigenvalue_ne_zero : eigenvalue ≠ 0) :
    Module.finrank ℂ (Module.End.eigenspace
        (((edgeSumMatrix S weight).conjTranspose * edgeSumMatrix S weight).mulVecLin)
        eigenvalue) =
      Module.finrank ℂ (Module.End.eigenspace
        (((edgeSumMatrix S weight) * (edgeSumMatrix S weight).conjTranspose).mulVecLin)
        eigenvalue) := by
  exact gram_eigenspace_finrank_eq (edgeSumMatrix S weight) eigenvalue
    hEigenvalue_ne_zero

end InfoGeometry.Canonical.PlabicGramEigenvectorTransport

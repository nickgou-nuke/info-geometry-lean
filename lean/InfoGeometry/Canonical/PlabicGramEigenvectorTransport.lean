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

end InfoGeometry.Canonical.PlabicGramEigenvectorTransport

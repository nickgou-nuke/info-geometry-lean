import InfoGeometry.Canonical.ZornFieldSpectralReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Associative spectral adapter for a quadratic Zorn readout

The native Zorn carrier is non-associative.  This file therefore introduces a
separate associative `2 × 2` complex matrix whose square parameter is the
scalar quadratic readout.  Eigenpairs are proved for this adapter only.
-/

namespace InfoGeometry.Canonical.ZornAssociativeSpectralAdapter

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVec3
open InfoGeometry.Canonical.ZornFieldSpectralReadout

def quadraticSpectralMatrix (q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, q; 1, 0]

def quadraticEigenvector (eig : ℂ) : Fin 2 → ℂ :=
  ![eig, 1]

def IsMatrixEigenpair
    (M : Matrix (Fin 2) (Fin 2) ℂ) (eig : ℂ) (v : Fin 2 → ℂ) : Prop :=
  M.mulVec v = eig • v ∧ v ≠ 0

theorem quadraticSpectralMatrix_eigenpair {q eig : ℂ}
    (heig : eig ^ 2 = q) :
    IsMatrixEigenpair (quadraticSpectralMatrix q) eig
      (quadraticEigenvector eig) := by
  constructor
  · ext i
    fin_cases i
    · simp [quadraticSpectralMatrix, quadraticEigenvector,
        Matrix.mulVec, dotProduct]
      rw [← heig, pow_two]
    · simp [quadraticSpectralMatrix, quadraticEigenvector,
        Matrix.mulVec, dotProduct]
  · intro hzero
    have h := congrFun hzero (1 : Fin 2)
    simp [quadraticEigenvector] at h

def fieldQuadraticSpectralMatrix
    (electric magnetic : ZornVec3 ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  quadraticSpectralMatrix
    ((dot magnetic magnetic - dot electric electric : ℝ) : ℂ)

theorem fieldQuadraticSpectralMatrix_eigenpair {electric magnetic : ZornVec3 ℝ}
    {eig : ℂ}
    (heig : eig ^ 2 =
      ((dot magnetic magnetic - dot electric electric : ℝ) : ℂ)) :
    IsMatrixEigenpair (fieldQuadraticSpectralMatrix electric magnetic) eig
      (quadraticEigenvector eig) := by
  exact quadraticSpectralMatrix_eigenpair heig

end InfoGeometry.Canonical.ZornAssociativeSpectralAdapter

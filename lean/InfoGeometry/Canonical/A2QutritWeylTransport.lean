import Mathlib.LinearAlgebra.Matrix.Permutation
import InfoGeometry.Canonical.A2QutritTransitionRootBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Weyl transport of the qutrit `A₂` transition roots

Permutation matrices give the concrete matrix realization of the coordinate
permutation action on the six ordered `A₂` roots.  This file proves the
conjugation identity directly for the matrix units.
-/

noncomputable section

namespace InfoGeometry.Canonical.A2QutritWeylTransport

open Matrix
open InfoGeometry.Canonical.A2InsideD5RootSubsystem
open InfoGeometry.Canonical.A2QutritTransitionRootBridge

abbrev QutritMatrix := InfoGeometry.Algebra.FiniteSpin.QutritMatrix

abbrev weylMatrix (σ : Equiv.Perm (Fin 3)) : QutritMatrix :=
  σ⁻¹.permMatrix ℂ

theorem weylMatrix_one : weylMatrix (1 : Equiv.Perm (Fin 3)) = 1 := by
  simp [weylMatrix]

theorem weylMatrix_mul (σ τ : Equiv.Perm (Fin 3)) :
    weylMatrix (σ * τ) = weylMatrix σ * weylMatrix τ := by
  simp [weylMatrix, Matrix.permMatrix_mul]

theorem weylMatrix_transpose (σ : Equiv.Perm (Fin 3)) :
    (weylMatrix σ)ᵀ = weylMatrix σ⁻¹ := by
  simp [weylMatrix]

theorem weylMatrix_inverse_mul (σ : Equiv.Perm (Fin 3)) :
    weylMatrix σ * (weylMatrix σ)ᵀ = 1 := by
  rw [weylMatrix_transpose, ← weylMatrix_mul]
  simp [weylMatrix]

theorem weylMatrix_mul_inverse (σ : Equiv.Perm (Fin 3)) :
    (weylMatrix σ)ᵀ * weylMatrix σ = 1 := by
  rw [weylMatrix_transpose, ← weylMatrix_mul]
  simp [weylMatrix]

theorem weylMatrix_conj_one (A : QutritMatrix) :
    weylMatrix (1 : Equiv.Perm (Fin 3)) * A *
        (weylMatrix (1 : Equiv.Perm (Fin 3)))ᵀ = A := by
  simp [weylMatrix]

theorem weylMatrix_conj_comp
    (σ τ : Equiv.Perm (Fin 3)) (A : QutritMatrix) :
    weylMatrix (σ * τ) * A * (weylMatrix (σ * τ))ᵀ =
      weylMatrix σ *
        (weylMatrix τ * A * (weylMatrix τ)ᵀ) * (weylMatrix σ)ᵀ := by
  rw [weylMatrix_mul, Matrix.transpose_mul]
  noncomm_ring

theorem weylMatrix_conj_transitionMatrix
    (σ : Equiv.Perm (Fin 3)) (r : A2Root) :
    weylMatrix σ * transitionMatrix r * (weylMatrix σ)ᵀ =
      transitionMatrix (weylAction σ r) := by
  rw [show (weylMatrix σ)ᵀ = weylMatrix σ⁻¹ by
    simp [weylMatrix]]
  simp only [weylMatrix, inv_inv]
  change ((σ⁻¹).toPEquiv.toMatrix * transitionMatrix r) *
      σ.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp only [transitionMatrix, Matrix.submatrix]
  by_cases hi : r.1.1 = σ.symm i
  · by_cases hj : r.1.2 = σ.symm j
    · simp [Matrix.single, hi, hj]
    · have hj' : σ r.1.2 ≠ j := by
        intro h
        apply hj
        rw [← h]
        simp
      simp [Matrix.single, hi, hj, hj']
  · have hi' : σ r.1.1 ≠ i := by
      intro h
      apply hi
      rw [← h]
      simp
    simp [Matrix.single, hi, hi']

theorem weylMatrix_conj_diagonalCartan
    (σ : Equiv.Perm (Fin 3)) (h : Fin 3 → ℂ) :
    weylMatrix σ * diagonalCartan h * (weylMatrix σ)ᵀ =
      diagonalCartan (h ∘ σ.symm) := by
  rw [show (weylMatrix σ)ᵀ = weylMatrix σ⁻¹ by
    simp [weylMatrix]]
  simp only [weylMatrix, inv_inv]
  change ((σ⁻¹).toPEquiv.toMatrix * diagonalCartan h) *
      σ.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [diagonalCartan, Matrix.submatrix]
  · simp [diagonalCartan, Matrix.submatrix, hij]

theorem weylMatrix_transport_root_eigenvalue
    (σ : Equiv.Perm (Fin 3)) (h : Fin 3 → ℂ) (r : A2Root) :
    diagonalCartan (h ∘ σ.symm) * transitionMatrix (weylAction σ r) -
        transitionMatrix (weylAction σ r) * diagonalCartan (h ∘ σ.symm) =
      (h r.1.1 - h r.1.2) • transitionMatrix (weylAction σ r) := by
  rw [diagonalCartan_comm_transitionMatrix]
  simp [weylAction]

end InfoGeometry.Canonical.A2QutritWeylTransport

end noncomputable section

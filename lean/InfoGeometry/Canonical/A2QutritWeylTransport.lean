/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Permutation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.A2QutritTransitionRootBridge

/-!
# Weyl transport of the qutrit `A₂` transition roots

Permutation matrices give the concrete matrix realization of the coordinate
permutation action on the six ordered `A₂` roots.  This file proves the
conjugation identity directly for the matrix units.

BUCKET 1: Finite qutrit permutation-matrix identities and the induced action
on transition matrices and diagonal Cartan operators.
BUCKET 2: No conditional theorem is asserted.
BUCKET 3: No arbitrary-ring representation, infinite root system, or Lie-group
integration result is claimed.
-/

noncomputable section

namespace InfoGeometry.Canonical.A2QutritWeylTransport

open Matrix
open InfoGeometry.Canonical.A2InsideD5RootSubsystem
open InfoGeometry.Canonical.A2QutritTransitionRootBridge

/-- The permutation representation in the qutrit matrix monoid. Its map laws
are carried by Mathlib's `MonoidHom` interface rather than exposed as separate
projection lemmas. -/
def weylMatrix : Equiv.Perm (Fin 3) →* InfoGeometry.Algebra.FiniteSpin.QutritMatrix where
  toFun σ := σ⁻¹.permMatrix ℂ
  map_one' := by simp
  map_mul' σ τ := by simp [Matrix.permMatrix_mul]

/-- The permutation representation is orthogonal: transpose represents the
inverse, and both matrix products with that transpose are the identity. -/
theorem weylMatrix_orthogonal (σ : Equiv.Perm (Fin 3)) :
    (weylMatrix σ)ᵀ = weylMatrix σ⁻¹ ∧
      weylMatrix σ * (weylMatrix σ)ᵀ = 1 ∧
      (weylMatrix σ)ᵀ * weylMatrix σ = 1 := by
  have htranspose : (weylMatrix σ)ᵀ = weylMatrix σ⁻¹ := by
    simp [weylMatrix]
  refine ⟨htranspose, ?_, ?_⟩
  · rw [htranspose, ← weylMatrix.map_mul]
    simp [weylMatrix]
  · rw [htranspose, ← weylMatrix.map_mul]
    simp [weylMatrix]

/-- Conjugation by a product of permutation matrices composes the two
coordinate actions in the same order. -/
theorem weylMatrix_conj_comp
    (σ τ : Equiv.Perm (Fin 3)) (A : InfoGeometry.Algebra.FiniteSpin.QutritMatrix) :
    weylMatrix (σ * τ) * A * (weylMatrix (σ * τ))ᵀ =
      weylMatrix σ *
        (weylMatrix τ * A * (weylMatrix τ)ᵀ) * (weylMatrix σ)ᵀ := by
  rw [weylMatrix.map_mul, Matrix.transpose_mul]
  noncomm_ring

/-- Conjugation transports each qutrit matrix unit along the coordinate Weyl
action on its ordered root. -/
theorem weylMatrix_conj_transitionMatrix
    (σ : Equiv.Perm (Fin 3)) (r : A2Root) :
    weylMatrix σ * transitionMatrix r * (weylMatrix σ)ᵀ =
      transitionMatrix (weylAction σ r) := by
  rw [(weylMatrix_orthogonal σ).1]
  simp only [weylMatrix]
  change ((σ⁻¹).toPEquiv.toMatrix * transitionMatrix r) *
      σ.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  have hroot := weylAction_preserves_root_data σ r
  have hroot_fst : (weylAction σ r).1.1 = σ r.1.1 := by
    exact congrArg Prod.fst hroot.1
  have hroot_snd : (weylAction σ r).1.2 = σ r.1.2 := by
    exact congrArg Prod.snd hroot.1
  ext i j
  simp only [transitionMatrix, Matrix.submatrix]
  by_cases hi : r.1.1 = σ.symm i
  · by_cases hj : r.1.2 = σ.symm j
    · simp [Matrix.single, hi, hj, hroot_fst, hroot_snd]
    · have hj' : σ r.1.2 ≠ j := by
        intro h
        apply hj
        rw [← h]
        simp
      simp [Matrix.single, hi, hj, hj', hroot_fst, hroot_snd]
  · have hi' : σ r.1.1 ≠ i := by
      intro h
      apply hi
      rw [← h]
      simp
    simp [Matrix.single, hi, hi', hroot_fst, hroot_snd]

/-- Conjugation transports a diagonal Cartan matrix by reindexing its
coordinate function by the inverse permutation. -/
theorem weylMatrix_conj_diagonalCartan
    (σ : Equiv.Perm (Fin 3)) (h : Fin 3 → ℂ) :
    weylMatrix σ * diagonalCartan h * (weylMatrix σ)ᵀ =
      diagonalCartan (h ∘ σ.symm) := by
  rw [(weylMatrix_orthogonal σ).1]
  simp only [weylMatrix]
  change ((σ⁻¹).toPEquiv.toMatrix * diagonalCartan h) *
      σ.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [diagonalCartan, Matrix.submatrix]
  · simp [diagonalCartan, Matrix.submatrix, hij]

/-- The diagonal Cartan eigenvalue of a transition root is preserved when
both the root and Cartan coordinates are transported together. -/
theorem weylMatrix_transport_root_eigenvalue
    (σ : Equiv.Perm (Fin 3)) (h : Fin 3 → ℂ) (r : A2Root) :
    diagonalCartan (h ∘ σ.symm) * transitionMatrix (weylAction σ r) -
        transitionMatrix (weylAction σ r) * diagonalCartan (h ∘ σ.symm) =
      (h r.1.1 - h r.1.2) • transitionMatrix (weylAction σ r) := by
  rw [diagonalCartan_comm_transitionMatrix]
  simp [weylAction]

end InfoGeometry.Canonical.A2QutritWeylTransport

end noncomputable section

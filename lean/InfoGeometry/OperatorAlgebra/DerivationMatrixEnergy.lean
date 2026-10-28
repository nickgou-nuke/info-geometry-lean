/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.DerivationGaugeTransport
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Positive matrix curvature energy

The coefficient algebra consists of all square real or complex matrices.
The energy uses the actual adjoint product `Xᴴ * X`. Unitary gauge invariance
is derived from the native star-algebra automorphism. A finite family of
Lie directions supplies the sum; for a basis, zero energy is equivalent to
vanishing of the entire native curvature two-cochain.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

open InfoGeometry.Algebra
open InfoGeometry.Geometry.AssociativeGaugeConnection
open scoped ComplexOrder

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The Hilbert--Schmidt norm square, expressed by the actual matrix trace. -/
def matrixTraceNormSq (X : Matrix n n 𝕜) : ℝ :=
  RCLike.re (Matrix.trace (star X * X))

omit [DecidableEq n] in
theorem matrixTraceNormSq_nonneg (X : Matrix n n 𝕜) :
    0 ≤ matrixTraceNormSq X := by
  exact (RCLike.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg).1

theorem matrixTraceNormSq_eq_zero_iff (X : Matrix n n 𝕜) :
    matrixTraceNormSq X = 0 ↔ X = 0 := by
  constructor
  · intro h
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    apply RCLike.ext
    · simpa only [matrixTraceNormSq, Matrix.star_eq_conjTranspose, map_zero] using h
    · simpa only [map_zero] using
        (RCLike.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg).2
  · rintro rfl
    simp [matrixTraceNormSq]

/-- The same multiplication-order-preserving conjugation used by the gauge action. -/
theorem conjugate_unitary_eq_starAlgAut
    (u : unitary (Matrix n n 𝕜)) (X : Matrix n n 𝕜) :
    conjugate (Unitary.toUnits u) X =
      Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) u X := rfl

/-- The adjoint trace pairing is invariant under unitary, possibly noncommuting,
changes of frame. -/
theorem matrixTraceNormSq_unitary_conjugate
    (u : unitary (Matrix n n 𝕜)) (X : Matrix n n 𝕜) :
    matrixTraceNormSq (conjugate (Unitary.toUnits u) X) = matrixTraceNormSq X := by
  let e := Unitary.conjStarAlgAut 𝕜 (Matrix n n 𝕜) u
  change RCLike.re (Matrix.trace (star (e X) * e X)) = _
  rw [← map_star e X, ← map_mul e (star X) X]
  change RCLike.re (Matrix.trace
      ((↑(Unitary.toUnits u) : Matrix n n 𝕜) * (star X * X) *
        (↑((Unitary.toUnits u)⁻¹) : Matrix n n 𝕜))) = _
  rw [Matrix.trace_units_conj]
  rfl

variable (K : DerivationLieLane ℝ (Matrix n n 𝕜))
variable {ι : Type*} [Fintype ι]

/-- A positive curvature functional for a specified finite frame of directions. -/
def matrixCurvatureEnergy (frame : ι → K.L) (Γ : OneForm K) : ℝ :=
  ∑ i, ∑ j, matrixTraceNormSq (connectionCurvature K Γ (frame i) (frame j))

theorem matrixCurvatureEnergy_nonneg (frame : ι → K.L) (Γ : OneForm K) :
    0 ≤ matrixCurvatureEnergy K frame Γ := by
  apply Finset.sum_nonneg
  intro i _
  exact Finset.sum_nonneg fun j _ => matrixTraceNormSq_nonneg _

theorem matrixCurvatureEnergy_eq_zero_iff (frame : ι → K.L) (Γ : OneForm K) :
    matrixCurvatureEnergy K frame Γ = 0 ↔
      ∀ i j, connectionCurvature K Γ (frame i) (frame j) = 0 := by
  unfold matrixCurvatureEnergy
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => matrixTraceNormSq_nonneg _))]
  simp only [Finset.mem_univ, forall_const]
  simp_rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => matrixTraceNormSq_nonneg _)]
  simp only [Finset.mem_univ, forall_const, matrixTraceNormSq_eq_zero_iff]

/-- A basis detects the full curvature; no positivity hypothesis is supplied. -/
theorem matrixCurvatureEnergy_basis_eq_zero_iff
    (b : Module.Basis ι ℝ K.L) (Γ : OneForm K) :
    matrixCurvatureEnergy K b Γ = 0 ↔ connectionCurvature K Γ = 0 := by
  rw [matrixCurvatureEnergy_eq_zero_iff]
  constructor
  · intro h
    apply Subtype.ext
    apply b.ext
    intro i
    apply b.ext
    intro j
    exact h i j
  · intro h i j
    rw [h]
    rfl

/-- Unitary gauge invariance of the positive full-matrix energy. -/
theorem matrixCurvatureEnergy_gaugeOneForm
    (frame : ι → K.L) (Γ : OneForm K) (u : unitary (Matrix n n 𝕜)) :
    matrixCurvatureEnergy K frame (gaugeOneForm K Γ (Unitary.toUnits u)) =
      matrixCurvatureEnergy K frame Γ := by
  simp only [matrixCurvatureEnergy, connectionCurvature_gaugeOneForm,
    matrixTraceNormSq_unitary_conjugate]

end InfoGeometry.OperatorAlgebra.DerivationDifferentialForms

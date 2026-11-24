/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermo.GenericMetriplecticFlow
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Real matrix realization of the existing GENERIC rate laws

Mathlib's `dotProductEquiv` identifies real finite coordinate vectors with their
algebraic dual. A skew matrix and a positive semidefinite matrix, with the two
specified degeneracies, therefore construct the existing covector-based system.
The first and second laws are obtained from that owner's theorems.

These are pointwise algebraic rate laws. No differentiable energy function,
trajectory, Jacobi identity, stationary state, or arithmetic zero is inferred.
-/

noncomputable section

namespace InfoGeometry.Thermo.MatrixGENERICRealization

open Matrix
open GenericMetriplecticFlow

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matrix acts on covectors through the native dot-product dual equivalence. -/
def matrixDualAction (A : Matrix ι ι ℝ) :
    Module.Dual ℝ (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  (Matrix.toLin' A).comp (dotProductEquiv ℝ ι).symm.toLinearMap

@[simp] theorem matrixDualAction_dotProductEquiv (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    matrixDualAction A (dotProductEquiv ℝ ι x) = A.mulVec x := by
  simp [matrixDualAction]

/-- The transpose identity supplies skewness for the actual covector action. -/
theorem matrixDualAction_skew (A : Matrix ι ι ℝ) (hA : Aᵀ = -A)
    (α β : Module.Dual ℝ (ι → ℝ)) :
    α (matrixDualAction A β) = -β (matrixDualAction A α) := by
  obtain ⟨x, rfl⟩ := (dotProductEquiv ℝ ι).surjective α
  obtain ⟨y, rfl⟩ := (dotProductEquiv ℝ ι).surjective β
  simp only [matrixDualAction_dotProductEquiv, dotProductEquiv_apply_apply]
  simpa [hA, Matrix.neg_mulVec] using (Matrix.dotProduct_transpose_mulVec A y x).symm

theorem matrixDualAction_symmetric (A : Matrix ι ι ℝ) (hA : Aᵀ = A)
    (α β : Module.Dual ℝ (ι → ℝ)) :
    α (matrixDualAction A β) = β (matrixDualAction A α) := by
  obtain ⟨x, rfl⟩ := (dotProductEquiv ℝ ι).surjective α
  obtain ⟨y, rfl⟩ := (dotProductEquiv ℝ ι).surjective β
  simp only [matrixDualAction_dotProductEquiv, dotProductEquiv_apply_apply]
  simpa [hA] using (Matrix.dotProduct_transpose_mulVec A y x).symm

theorem matrixDualAction_nonneg (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (α : Module.Dual ℝ (ι → ℝ)) : 0 ≤ α (matrixDualAction A α) := by
  obtain ⟨x, rfl⟩ := (dotProductEquiv ℝ ι).surjective α
  simpa using hA.dotProduct_mulVec_nonneg x

/-- Construct the owned GENERIC system from real matrices and explicit degeneracies. -/
def matrixSystem (L M : Matrix ι ι ℝ) (hL : Lᵀ = -L) (hM : M.PosSemidef)
    (gradH gradS : ι → ℝ) (hDegH : M.mulVec gradH = 0)
    (hDegS : L.mulVec gradS = 0) : System (ι → ℝ) where
  dH := dotProductEquiv ℝ ι gradH
  dS := dotProductEquiv ℝ ι gradS
  L := matrixDualAction L
  M := matrixDualAction M
  L_skew := matrixDualAction_skew L hL
  L_entropy_casimir := by simpa using hDegS
  M_symmetric := matrixDualAction_symmetric M (by simpa using hM.isHermitian.eq)
  M_hamiltonian_casimir := by simpa using hDegH
  M_nonneg := matrixDualAction_nonneg M hM

@[simp] theorem matrixSystem_flow (L M : Matrix ι ι ℝ) (hL : Lᵀ = -L)
    (hM : M.PosSemidef) (gradH gradS : ι → ℝ)
    (hDegH : M.mulVec gradH = 0) (hDegS : L.mulVec gradS = 0) :
    (matrixSystem L M hL hM gradH gradS hDegH hDegS).flow =
      L.mulVec gradH + M.mulVec gradS := by
  simp [System.flow, matrixSystem]

/-- The existing abstract energy theorem specializes to the displayed matrix flow. -/
theorem energy_rate_eq_zero (L M : Matrix ι ι ℝ) (hL : Lᵀ = -L)
    (hM : M.PosSemidef) (gradH gradS : ι → ℝ)
    (hDegH : M.mulVec gradH = 0) (hDegS : L.mulVec gradS = 0) :
    dotProduct gradH (L.mulVec gradH + M.mulVec gradS) = 0 := by
  simpa [matrixSystem, System.flow] using
    (matrixSystem L M hL hM gradH gradS hDegH hDegS).energy_rate

/-- The entropy rate is the native positive semidefinite quadratic form. -/
theorem entropy_rate_eq_dissipative (L M : Matrix ι ι ℝ) (hL : Lᵀ = -L)
    (hM : M.PosSemidef) (gradH gradS : ι → ℝ)
    (hDegH : M.mulVec gradH = 0) (hDegS : L.mulVec gradS = 0) :
    dotProduct gradS (L.mulVec gradH + M.mulVec gradS) =
      dotProduct gradS (M.mulVec gradS) := by
  simpa [matrixSystem, System.flow] using
    (matrixSystem L M hL hM gradH gradS hDegH hDegS).entropy_rate_eq_dissipative

theorem entropy_rate_nonneg (L M : Matrix ι ι ℝ) (hL : Lᵀ = -L)
    (hM : M.PosSemidef) (gradH gradS : ι → ℝ)
    (hDegH : M.mulVec gradH = 0) (hDegS : L.mulVec gradS = 0) :
    0 ≤ dotProduct gradS (L.mulVec gradH + M.mulVec gradS) := by
  simpa [matrixSystem, System.flow] using
    (matrixSystem L M hL hM gradH gradS hDegH hDegS).entropy_rate_nonneg

omit [DecidableEq ι] in
/-- An invertible reversible action and the entropy degeneracy force zero entropy gradient. -/
theorem entropy_gradient_eq_zero_of_injective (L : Matrix ι ι ℝ)
    (hL : Function.Injective L.mulVec) (gradS : ι → ℝ)
    (hDegS : L.mulVec gradS = 0) : gradS = 0 := by
  apply hL
  simpa using hDegS

end InfoGeometry.Thermo.MatrixGENERICRealization

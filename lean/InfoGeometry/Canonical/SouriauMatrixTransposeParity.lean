/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Canonical.NormalizedTracePositivity
import InfoGeometry.Canonical.SouriauCoadjointOrbitBridge
import InfoGeometry.Canonical.SouriauKKSForm
import InfoGeometry.Thermo.OnsagerOperatorClosure

/-!
# Matrix transpose parity for the Souriau KKS form

This owner supplies a concrete, non-axiomatic parity model for the full real
matrix Lie algebra.  Every identity is derived from the associative matrix
product, transpose, and Mathlib's trace lemmas.  No generic time-reversal,
momentum-invariance, or Fisher-evenness proposition is postulated.
-/

noncomputable section

open scoped Matrix

namespace InfoGeometry.Canonical.SouriauMatrixTransposeParity

open InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem
open InfoGeometry.Canonical.SouriauCoadjointOrbitBridge
open SouriauKKS

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance : LieRing (Matrix n n ℝ) := LieRing.ofAssociativeRing
local instance : LieAlgebra ℝ (Matrix n n ℝ) := LieAlgebra.ofAssociativeAlgebra

/-- The transpose as a real-linear involution of the matrix Lie algebra. -/
def matrixTransposeLinearMap : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ where
  toFun := Matrix.transpose
  map_add' := by
    intro X Y
    simp
  map_smul' := by
    intro r X
    simp

/-- The matrix transpose time reversal. -/
def matrixTransposeTimeReversal : TimeReversal (Matrix n n ℝ) where
  op := matrixTransposeLinearMap
  involutive := by
    intro X
    exact Matrix.transpose_transpose X

omit [Fintype n] [DecidableEq n] in
@[simp] theorem matrixTransposeTimeReversal_apply (X : Matrix n n ℝ) :
    matrixTransposeTimeReversal.op X = Xᵀ := rfl

/-- Transpose reverses the commutator bracket. -/
theorem matrixTranspose_bracket_reversal (X Y : Matrix n n ℝ) :
    ⁅matrixTransposeTimeReversal.op X, matrixTransposeTimeReversal.op Y⁆ =
      -matrixTransposeTimeReversal.op ⁅X, Y⁆ := by
  change ⁅Xᵀ, Yᵀ⁆ = -⁅X, Y⁆ᵀ
  rw [LieRing.of_associative_ring_bracket,
    LieRing.of_associative_ring_bracket]
  simp only [Matrix.transpose_sub, Matrix.transpose_mul]
  abel

/-- The trace pairing with a fixed symmetric matrix is transpose invariant. -/
def matrixTracePairing (A : Matrix n n ℝ) : Module.Dual ℝ (Matrix n n ℝ) where
  toFun X := Matrix.trace (Aᵀ * X)
  map_add' := by
    intro X Y
    simp [Matrix.mul_add]
  map_smul' := by
    intro r X
    simp

theorem matrixTracePairing_transpose_of_symmetric
    (A X : Matrix n n ℝ) (hA : Aᵀ = A) :
    matrixTracePairing A Xᵀ = matrixTracePairing A X := by
  unfold matrixTracePairing
  calc
    Matrix.trace (Aᵀ * Xᵀ) = Matrix.trace ((Aᵀ * Xᵀ)ᵀ) :=
      (Matrix.trace_transpose _).symm
    _ = Matrix.trace (X * A) := by
      simp [Matrix.transpose_mul, hA]
    _ = Matrix.trace (A * X) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Aᵀ * X) := by rw [hA]

/-- The KKS response of a symmetric trace momentum is transpose odd. -/
theorem matrixTraceKKS_transpose_odd
    (A X Y : Matrix n n ℝ) (hA : Aᵀ = A) :
    kksForm (R := ℝ) (matrixTracePairing A)
        (matrixTransposeTimeReversal.op X) (matrixTransposeTimeReversal.op Y) =
      -kksForm (R := ℝ) (matrixTracePairing A) X Y := by
  unfold kksForm
  rw [matrixTranspose_bracket_reversal,
    (matrixTracePairing A).map_neg,
    matrixTransposeTimeReversal_apply,
    matrixTracePairing_transpose_of_symmetric A _ hA]

/-- The native Frobenius trace form on matrices. -/
def matrixFisherMetric : LinearMap.BilinForm ℝ (Matrix n n ℝ) :=
  LinearMap.mk₂ ℝ (fun X Y : Matrix n n ℝ => Matrix.trace (Xᵀ * Y))
    (by
      intro X₁ X₂ Y
      simp [Matrix.add_mul])
    (by
      intro r X Y
      simp)
    (by
      intro X Y₁ Y₂
      simp [Matrix.mul_add])
    (by
      intro r X Y
      simp)

@[simp] theorem matrixFisherMetric_apply (X Y : Matrix n n ℝ) :
    matrixFisherMetric X Y = Matrix.trace (Xᵀ * Y) := rfl

theorem matrixFisherMetric_symmetric (X Y : Matrix n n ℝ) :
    matrixFisherMetric X Y = matrixFisherMetric Y X := by
  calc
    Matrix.trace (Xᵀ * Y) = Matrix.trace ((Xᵀ * Y)ᵀ) :=
      (Matrix.trace_transpose _).symm
    _ = Matrix.trace (Yᵀ * X) := by simp [Matrix.transpose_mul]

theorem matrixFisherMetric_nonneg (X : Matrix n n ℝ) :
    0 ≤ matrixFisherMetric X X := by
  simpa [matrixFisherMetric] using
    NormalizedTracePositivity.trace_transpose_mul_self_nonneg X

theorem matrixFisherMetric_transpose_even (X Y : Matrix n n ℝ) :
    matrixFisherMetric (matrixTransposeTimeReversal.op X)
        (matrixTransposeTimeReversal.op Y) =
      matrixFisherMetric X Y := by
  calc
    Matrix.trace ((Xᵀ)ᵀ * Yᵀ) = Matrix.trace (X * Yᵀ) := by
      simp
    _ = Matrix.trace ((X * Yᵀ)ᵀ) := (Matrix.trace_transpose _).symm
    _ = Matrix.trace (Y * Xᵀ) := by simp [Matrix.transpose_mul]
    _ = Matrix.trace (Xᵀ * Y) := Matrix.trace_mul_comm _ _

/-- The concrete matrix Fisher/KKS Onsager system. -/
def matrixTransposeOnsagerSystem (A : Matrix n n ℝ) :
    InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem (Matrix n n ℝ) :=
  souriauOnsagerSystem matrixFisherMetric (matrixTracePairing A)
    matrixFisherMetric_symmetric matrixFisherMetric_nonneg

/-- Transpose reciprocity for the concrete symmetric trace-momentum system. -/
theorem matrixTransposeOnsager_master_reciprocity
    (A : Matrix n n ℝ) (hA : Aᵀ = A) (X Y : Matrix n n ℝ) :
    (matrixTransposeOnsagerSystem A).totalGenerator
        (matrixTransposeTimeReversal.op X) (matrixTransposeTimeReversal.op Y) =
      (matrixTransposeOnsagerSystem A).totalGenerator Y X := by
  change
    (matrixFisherMetric (matrixTransposeTimeReversal.op X)
        (matrixTransposeTimeReversal.op Y) +
      souriauKKSBilinForm (matrixTracePairing A)
        (matrixTransposeTimeReversal.op X) (matrixTransposeTimeReversal.op Y)) =
      (matrixFisherMetric Y X +
        souriauKKSBilinForm (matrixTracePairing A) Y X)
  rw [matrixFisherMetric_transpose_even, matrixFisherMetric_symmetric]
  change
    matrixFisherMetric Y X +
        kksForm (R := ℝ) (matrixTracePairing A)
          (matrixTransposeTimeReversal.op X) (matrixTransposeTimeReversal.op Y) =
      matrixFisherMetric Y X + kksForm (R := ℝ) (matrixTracePairing A) Y X
  rw [matrixTraceKKS_transpose_odd A X Y hA, kksForm_skew]
  ring_nf

end InfoGeometry.Canonical.SouriauMatrixTransposeParity

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.PeirceParity
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.HodgeKernel

/-!
# Orthogonal Peirce parity and the native matrix adjoint

Trace preservation and star compatibility are proved for the actual reflection
of an orthogonal projection. This supplies the geometric hypotheses of the
Hilbert–Schmidt calculation without postulating its conclusion.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSuperoperators

open Matrix
open scoped ComplexOrder

open InfoGeometry.Core
open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint

attribute [local instance] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance : NormedAddCommGroup (Matrix n n ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance : InnerProductSpace ℂ (Matrix n n ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

theorem parityEquiv_trace (p : Matrix n n ℂ) (hp : IsIdempotentElem p)
    (X : Matrix n n ℂ) :
    Matrix.trace (parityEquiv (R := ℂ) p hp X) = Matrix.trace X := by
  rw [parityEquiv_apply, Matrix.trace_mul_cycle,
    PeirceGrading.reflection_sq hp, one_mul]

/-- The actual Peirce involution is self-adjoint for the native matrix metric. -/
theorem peirce_parity_adjoint (p : Matrix n n ℂ) (hp : IsStarProjection p) :
    (parityEquiv (R := ℂ) p hp.isIdempotentElem).toLinearMap.adjoint =
      (parityEquiv (R := ℂ) p hp.isIdempotentElem).toLinearMap :=
  hs_adjoint_parity _ (parityEquiv_involutive p hp.isIdempotentElem)
    (parityEquiv_star p hp.isIdempotentElem hp.isSelfAdjoint)
    (parityEquiv_trace p hp.isIdempotentElem)

/-- The metric adjoint for an actually odd Peirce charge. -/
theorem peirce_graded_adjoint (p : Matrix n n ℂ) (hp : IsStarProjection p)
    (N : Matrix n n ℂ) (hN : N ∈ LinearMap.range (PeirceGrading.odd p)) :
    (gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) N).adjoint =
      LinearMap.mulLeft ℂ Nᴴ + (LinearMap.mulRight ℂ Nᴴ).comp
        (parityEquiv (R := ℂ) p hp.isIdempotentElem).toLinearMap :=
  gradedAdjoint_adjoint _ (parityEquiv_involutive p hp.isIdempotentElem)
    (parityEquiv_star p hp.isIdempotentElem hp.isSelfAdjoint)
    (parityEquiv_trace p hp.isIdempotentElem) N (parityEquiv_of_odd hp.isIdempotentElem hN)

/-- The positive Hodge operator of the actual Peirce graded action is Jordan multiplication. -/
theorem peirce_graded_hodge (p : Matrix n n ℂ) (hp : IsStarProjection p)
    (N : Matrix n n ℂ) (hN : N ∈ LinearMap.range (PeirceGrading.odd p)) :
    gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) N *
        (gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) N).adjoint +
      (gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) N).adjoint *
        gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) N =
      jordanLeft (R := ℂ) (N * Nᴴ + Nᴴ * N) :=
  gradedAdjoint_hodge _ (parityEquiv_involutive p hp.isIdempotentElem)
    (parityEquiv_star p hp.isIdempotentElem hp.isSelfAdjoint)
    (parityEquiv_trace p hp.isIdempotentElem) N (parityEquiv_of_odd hp.isIdempotentElem hN)

/-- Substituting the conjugate-transposed charge gives the different, inner Lie curvature. -/
theorem peirce_graded_mixed (p : Matrix n n ℂ) (hp : IsStarProjection p)
    (N : Matrix n n ℂ) (hN : N ∈ LinearMap.range (PeirceGrading.odd p)) :
    gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) N *
        gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) Nᴴ +
      gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) Nᴴ *
        gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) N =
      LieAlgebra.ad ℂ (Matrix n n ℂ) (N * Nᴴ + Nᴴ * N) := by
  have hodd := parityEquiv_of_odd (R := ℂ) hp.isIdempotentElem hN
  have hstar : parityEquiv (R := ℂ) p hp.isIdempotentElem Nᴴ = -Nᴴ := by
    calc
      _ = (parityEquiv (R := ℂ) p hp.isIdempotentElem N)ᴴ :=
        parityEquiv_star p hp.isIdempotentElem hp.isSelfAdjoint N
      _ = -Nᴴ := by rw [hodd, Matrix.conjTranspose_neg]
  exact gradedAdjoint_mixed _ (parityEquiv_involutive p hp.isIdempotentElem) N Nᴴ hodd hstar

/-- The joint graded kernel lies in the Gram centralizer; equality is not asserted. -/
theorem joint_graded_ker_le_centralizer (p : Matrix n n ℂ) (hp : IsStarProjection p)
    (N : Matrix n n ℂ) (hN : N ∈ LinearMap.range (PeirceGrading.odd p)) :
    (gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) N).ker ⊓
        (gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) Nᴴ).ker ≤
      (LieAlgebra.ad ℂ (Matrix n n ℂ) (N * Nᴴ + Nᴴ * N)).ker := by
  intro X hX
  have h₁ : gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) N X = 0 := hX.1
  have h₂ : gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) Nᴴ X = 0 := hX.2
  rw [← peirce_graded_mixed p hp N hN]
  change gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) N
      (gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) Nᴴ X) +
    gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) Nᴴ
      (gradedAdjoint (parityEquiv (R := ℂ) p hp.isIdempotentElem) N X) = 0
  rw [h₁, h₂, map_zero, map_zero, add_zero]

end InfoGeometry.OperatorAlgebra.PeirceSuperoperators

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.FiniteRealFockNormBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Finite real quadratic Fock operators and their adjoints

The carrier and positive metric are the existing `SpinorSpace (Vector n)` and
the named induced structures from `FiniteRealFockMetric`. The operator attached
to a real coefficient matrix is the finite sum of the actual continuous
creation-after-contraction operators. Its adjoint transposes the coefficients;
symmetry of the coefficient matrix therefore gives a genuine self-adjoint
bounded operator on this positive real Hilbert space.

No scalar complexification, new Fock carrier, or assumed adjoint law is used.
Completeness below follows from the existing finite exterior basis. This file
does not yet identify the finite sum with `CliffordExteriorLift.exteriorLift`.
-/

noncomputable section

namespace InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

open InfoGeometry.Clifford
open scoped BigOperators

attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

/-- Finite-dimensionality is supplied by the actual exterior basis. -/
local instance fockQuadraticFiniteDimensional (n : ℕ) :
    FiniteDimensional ℝ (SpinorSpace (Vector n)) :=
  ((Pi.basisFun ℝ (Fin n)).ExteriorAlgebra).finiteDimensional_of_finite

/-- The existing positive Fock metric is complete in finite dimension. -/
local instance fockQuadraticCompleteSpace (n : ℕ) :
    CompleteSpace (SpinorSpace (Vector n)) :=
  FiniteDimensional.complete ℝ (SpinorSpace (Vector n))

/-- Real coefficient matrix acting by creation after contraction on the
entire finite exterior-Fock carrier. The order is `C_i ∘ A_j`. -/
def fockQuadraticCLM (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    SpinorSpace (Vector n) →L[ℝ] SpinorSpace (Vector n) :=
  ∑ i : Fin n, ∑ j : Fin n,
    M i j • (fockExtActionCLM n i).comp (fockIntActionCLM n j)

@[simp] theorem fockQuadraticCLM_apply (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (x : SpinorSpace (Vector n)) :
    fockQuadraticCLM n M x =
      ∑ i : Fin n, ∑ j : Fin n,
        M i j • fockExtActionCLM n i (fockIntActionCLM n j x) := by
  simp only [fockQuadraticCLM, sum_apply, smul_apply, ContinuousLinearMap.comp_apply]

@[simp] theorem fockQuadraticCLM_smul (n : ℕ) (r : ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    fockQuadraticCLM n (r • M) = r • fockQuadraticCLM n M := by
  change (∑ i : Fin n, ∑ j : Fin n,
      (r * M i j) • (fockExtActionCLM n i).comp (fockIntActionCLM n j)) =
    r • (∑ i : Fin n, ∑ j : Fin n,
      M i j • (fockExtActionCLM n i).comp (fockIntActionCLM n j))
  simp only [mul_smul, Finset.smul_sum]

@[simp] theorem fockQuadraticCLM_neg (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    fockQuadraticCLM n (-M) = -fockQuadraticCLM n M := by
  simpa only [neg_one_smul] using fockQuadraticCLM_smul n (-1) M

/-- The actual real bilinear adjoint identity, derived term by term from
the native creation/contraction pairing. Transposition exchanges the mode
indices after reversing operator composition. -/
theorem fockQuadraticCLM_inner_transpose (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (x y : SpinorSpace (Vector n)) :
    inner ℝ (fockQuadraticCLM n M x) y =
      inner ℝ x (fockQuadraticCLM n M.transpose y) := by
  have hmode (i j : Fin n) :
      inner ℝ (fockExtActionCLM n i (fockIntActionCLM n j x)) y =
        inner ℝ x (fockExtActionCLM n j (fockIntActionCLM n i y)) := by
    calc
      _ = inner ℝ (fockIntActionCLM n j x) (fockIntActionCLM n i y) :=
        fock_extAction_intAction_inner n i (fockIntActionCLM n j x) y
      _ = inner ℝ (fockIntActionCLM n i y) (fockIntActionCLM n j x) :=
        real_inner_comm _ _
      _ = inner ℝ (fockExtActionCLM n j (fockIntActionCLM n i y)) x :=
        (fock_extAction_intAction_inner n j (fockIntActionCLM n i y) x).symm
      _ = _ := real_inner_comm _ _
  simp only [fockQuadraticCLM_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, hmode, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- The genuine Hilbert adjoint of the finite quadratic operator is the
quadratic operator of the transposed real coefficient matrix. -/
@[simp] theorem fockQuadraticCLM_adjoint (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    (fockQuadraticCLM n M).adjoint = fockQuadraticCLM n M.transpose := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    (fockQuadraticCLM n M.transpose) (fockQuadraticCLM n M)).2
  intro x y
  simpa only [Matrix.transpose_transpose] using
    fockQuadraticCLM_inner_transpose n M.transpose x y

/-- Symmetric real coefficients produce a self-adjoint bounded Fock
operator, without a diagonal or commuting-coefficient hypothesis. -/
theorem fockQuadraticCLM_isSelfAdjoint (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    IsSelfAdjoint (fockQuadraticCLM n M) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', fockQuadraticCLM_adjoint, hM.eq]

/-- Skew-symmetric real coefficients produce a skew-adjoint operator on
the same positive Hilbert carrier. -/
theorem fockQuadraticCLM_adjoint_of_transpose_eq_neg (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.transpose = -M) :
    (fockQuadraticCLM n M).adjoint = -fockQuadraticCLM n M := by
  rw [fockQuadraticCLM_adjoint, hM, fockQuadraticCLM_neg]

end InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

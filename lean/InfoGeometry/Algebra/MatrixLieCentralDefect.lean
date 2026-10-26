/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Lie.Cochain
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Scalar defects of finite real matrix Lie lifts

The trace splits a scalar bracket defect. This is a statement about a linear
Lie lift, not an arbitrary manifold connection, a gauge transformation, or
the vanishing of all Lie algebra cohomology. Scalar coefficients use the
native trivial Lie module and native low-degree CE differential.
-/

noncomputable section

namespace InfoGeometry.Algebra.MatrixLieCentralDefect

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Central scalar shifts do not affect the adjoint action. -/
theorem commutator_add_scalar (B U : Matrix n n ℝ) (c : ℝ) :
    (B + c • 1) * U - U * (B + c • 1) = B * U - U * B := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  abel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

def defect (A : L →ₗ[ℝ] Matrix n n ℝ) (x y : L) : Matrix n n ℝ :=
  A x * A y - A y * A x - A ⁅x, y⁆

/-- A scalar defect has zero adjoint action on every matrix observable. -/
theorem scalar_defect_adjoint_zero (A : L →ₗ[ℝ] Matrix n n ℝ)
    (x y : L) (c : ℝ) (h : defect A x y = c • 1) (U : Matrix n n ℝ) :
    defect A x y * U - U * defect A x y = 0 := by
  rw [h]
  simp

def tracePotential (A : L →ₗ[ℝ] Matrix n n ℝ) : L →ₗ[ℝ] ℝ :=
  (Fintype.card n : ℝ)⁻¹ • ((Matrix.traceLinearMap n ℝ ℝ).comp A)

omit [DecidableEq n] in
@[simp] theorem tracePotential_apply (A : L →ₗ[ℝ] Matrix n n ℝ) (x : L) :
    tracePotential A x = (Fintype.card n : ℝ)⁻¹ * (A x).trace := rfl

def traceCochain (A : L →ₗ[ℝ] Matrix n n ℝ) :
    LieModule.Cohomology.oneCochain ℝ L (TrivialLieModule ℝ L ℝ) :=
  (TrivialLieModule.equiv ℝ L ℝ).symm.toLinearMap.comp (tracePotential A)

def traceCoboundary (A : L →ₗ[ℝ] Matrix n n ℝ) :
    LieModule.Cohomology.twoCochain ℝ L (TrivialLieModule ℝ L ℝ) :=
  LieModule.Cohomology.d₁₂ ℝ L _ (traceCochain A)

omit [DecidableEq n] in
theorem traceCoboundary_apply (A : L →ₗ[ℝ] Matrix n n ℝ) (x y : L) :
    (TrivialLieModule.equiv ℝ L ℝ) (traceCoboundary A x y) =
      -tracePotential A ⁅x, y⁆ := by
  rw [traceCoboundary, LieModule.Cohomology.d₁₂_apply_apply_ofTrivial]
  rfl

omit [DecidableEq n] in
theorem traceCoboundary_is_cocycle (A : L →ₗ[ℝ] Matrix n n ℝ) :
    LieModule.Cohomology.d₂₃ ℝ L _ (traceCoboundary A) = 0 := by
  exact LinearMap.congr_fun
    (LieModule.Cohomology.d₂₃_comp_d₁₂ ℝ L (TrivialLieModule ℝ L ℝ))
    (traceCochain A)

theorem scalar_defect_coefficient [Nonempty n]
    (A : L →ₗ[ℝ] Matrix n n ℝ) (x y : L) (c : ℝ)
    (h : defect A x y = c • 1) : c = -tracePotential A ⁅x, y⁆ := by
  have hn : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ht := congrArg Matrix.trace h
  simp only [defect, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    smul_eq_mul] at ht
  rw [Matrix.trace_mul_comm (A x) (A y)] at ht
  simp only [sub_self, zero_sub] at ht
  calc
    c = (-(A ⁅x, y⁆).trace) / (Fintype.card n : ℝ) :=
      (eq_div_iff hn).2 ht.symm
    _ = -tracePotential A ⁅x, y⁆ := by
      simp [tracePotential_apply, div_eq_mul_inv, mul_comm]

/-- The scalar defect is the native CE coboundary, with trivial coefficients. -/
theorem scalar_defect_is_coboundary [Nonempty n]
    (A : L →ₗ[ℝ] Matrix n n ℝ) (x y : L) (c : ℝ)
    (h : defect A x y = c • 1) :
    c = (TrivialLieModule.equiv ℝ L ℝ) (traceCoboundary A x y) := by
  rw [traceCoboundary_apply]
  exact scalar_defect_coefficient A x y c h

def traceFreeLift (A : L →ₗ[ℝ] Matrix n n ℝ) : L →ₗ[ℝ] Matrix n n ℝ :=
  A - (Algebra.linearMap ℝ (Matrix n n ℝ)).comp (tracePotential A)

@[simp] theorem traceFreeLift_apply (A : L →ₗ[ℝ] Matrix n n ℝ) (x : L) :
    traceFreeLift A x = A x - tracePotential A x • 1 := by
  simp [traceFreeLift, Algebra.algebraMap_eq_smul_one]

theorem traceFreeLift_trace [Nonempty n] (A : L →ₗ[ℝ] Matrix n n ℝ) (x : L) :
    (traceFreeLift A x).trace = 0 := by
  have hn : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [traceFreeLift_apply, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, tracePotential_apply, smul_eq_mul]
  simp [mul_comm, hn]

theorem traceFreeLift_commutator (A : L →ₗ[ℝ] Matrix n n ℝ) (x y : L) :
    traceFreeLift A x * traceFreeLift A y -
        traceFreeLift A y * traceFreeLift A x = A x * A y - A y * A x := by
  simp only [traceFreeLift_apply, sub_mul, mul_sub, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, smul_sub, smul_smul]
  rw [mul_comm (tracePotential A x) (tracePotential A y)]
  abel

/-- A scalar-defective lift has an honest trace-normalized Lie representation. -/
def normalizedLieHom [Nonempty n] (A : L →ₗ[ℝ] Matrix n n ℝ)
    (h : ∀ x y, ∃ c : ℝ, defect A x y = c • 1) :
    L →ₗ⁅ℝ⁆ Matrix n n ℝ :=
  { traceFreeLift A with
    map_lie' := by
      intro x y
      change traceFreeLift A ⁅x, y⁆ =
        traceFreeLift A x * traceFreeLift A y - traceFreeLift A y * traceFreeLift A x
      rw [traceFreeLift_commutator, traceFreeLift_apply]
      obtain ⟨c, hc⟩ := h x y
      have ht := scalar_defect_coefficient A x y c hc
      rw [ht, neg_smul] at hc
      dsimp [defect] at hc
      simpa only [tracePotential_apply, sub_eq_add_neg, add_comm] using
        (sub_eq_iff_eq_add.mp hc).symm }

end InfoGeometry.Algebra.MatrixLieCentralDefect

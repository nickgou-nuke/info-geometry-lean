/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Lie.Cochain
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Matrix curvature in the cyclic coefficient module

The quotient kills the linear span of commutators, not a two-sided ideal.
Exactness below is quotient-valued; it does not flatten the original connection.
No commutativity of the coefficient algebra is assumed.
-/

namespace InfoGeometry.Algebra.CyclicMatrixCurvature

variable (R A : Type*) [CommRing R] [Ring A] [Algebra R A]

/-- The additive R-linear commutator span. -/
def commutatorSpan : Submodule R A :=
  Submodule.span R {c | ∃ a b : A, c = a * b - b * a}

abbrev CyclicModule := A ⧸ commutatorSpan R A

def cyclicClass : A →ₗ[R] CyclicModule R A :=
  (commutatorSpan R A).mkQ

theorem cyclicClass_commutator (a b : A) :
    cyclicClass R A (a * b - b * a) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero (commutatorSpan R A)).mpr
  exact Submodule.subset_span ⟨a, b, rfl⟩

theorem cyclicClass_mul_comm (a b : A) :
    cyclicClass R A (a * b) = cyclicClass R A (b * a) := by
  have h := cyclicClass_commutator R A a b
  rw [map_sub, sub_eq_zero] at h
  exact h

variable {n : Type*} [Fintype n]

/-- Native matrix trace followed by the coefficient quotient. -/
def cyclicTrace : Matrix n n A →ₗ[R] CyclicModule R A :=
  (cyclicClass R A).comp (Matrix.traceLinearMap n R A)

theorem cyclicTrace_mul_comm (X Y : Matrix n n A) :
    cyclicTrace R A (X * Y) = cyclicTrace R A (Y * X) := by
  change cyclicClass R A (Matrix.trace (X * Y)) =
    cyclicClass R A (Matrix.trace (Y * X))
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact cyclicClass_mul_comm R A _ _

theorem cyclicTrace_commutator (X Y : Matrix n n A) :
    cyclicTrace R A (X * Y - Y * X) = 0 := by
  rw [map_sub, cyclicTrace_mul_comm, sub_self]

theorem cyclicTrace_diagonal [DecidableEq n] (a : A) :
    cyclicTrace R A (Matrix.diagonal (fun _ : n => a)) =
      (Fintype.card n : R) • cyclicClass R A a := by
  change cyclicClass R A (Matrix.trace (Matrix.diagonal (fun _ : n => a))) = _
  simp only [Matrix.trace_diagonal, Finset.sum_const, Finset.card_univ,
    map_nsmul, Nat.cast_smul_eq_nsmul]

section Cohomology

variable {L : Type*} [LieRing L] [LieAlgebra R L]

abbrev Coefficients := TrivialLieModule R L (CyclicModule R A)

/-- A normalization coefficient is explicit; no division by a nonunit. -/
def tracePotential (s : R) (C : L →ₗ[R] Matrix n n A) :
    L →ₗ[R] Coefficients R A (L := L) :=
  (TrivialLieModule.equiv R L (CyclicModule R A)).symm.toLinearMap.comp
    (s • (cyclicTrace R A).comp C)

open LieModule.Cohomology

/-- The cyclic image of a diagonal defect is a native CE coboundary.
Centrality of the diagonal coefficient is not needed for this trace statement. -/
theorem scalar_defect_eq_coboundary [DecidableEq n]
    (s : R) (hs : s * (Fintype.card n : R) = 1)
    (C : L →ₗ[R] Matrix n n A) (ω : L → L → A)
    (hF : ∀ x y, C x * C y - C y * C x - C ⁅x, y⁆ =
      Matrix.diagonal (fun _ : n => ω x y)) (x y : L) :
    (TrivialLieModule.equiv R L (CyclicModule R A)).symm
        (cyclicClass R A (ω x y)) =
      d₁₂ R L (Coefficients R A (L := L)) (tracePotential R A s C) x y := by
  rw [d₁₂_apply_apply_ofTrivial]
  apply (TrivialLieModule.equiv R L (CyclicModule R A)).injective
  change cyclicClass R A (ω x y) = - (s • cyclicTrace R A (C ⁅x, y⁆))
  have ht := congrArg (cyclicTrace R A) (hF x y)
  rw [map_sub, cyclicTrace_commutator, zero_sub, cyclicTrace_diagonal] at ht
  have h := congrArg (fun z : CyclicModule R A => s • z) ht
  simpa only [smul_neg, smul_smul, hs, one_smul] using h.symm

theorem tracePotential_coboundary_is_cocycle
    (s : R) (C : L →ₗ[R] Matrix n n A) :
    d₁₂ R L (Coefficients R A (L := L)) (tracePotential R A s C) ∈
      twoCocycle R L (Coefficients R A (L := L)) := by
  rw [mem_twoCocycle_iff]
  have h := LinearMap.congr_fun
    (d₂₃_comp_d₁₂ R L (Coefficients R A (L := L))) (tracePotential R A s C)
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h

end Cohomology
end InfoGeometry.Algebra.CyclicMatrixCurvature

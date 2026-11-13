/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CyclicMatrixCurvature
import InfoGeometry.Geometry.AssociativeGaugeConnection
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Matrix derivatives and cyclic curvature balance

Native `LinearMap.mapMatrix` lifts a coefficient derivation. The raw trace
retains the trace of the commutator. The existing cyclic coefficient quotient
removes it, and the coefficient derivation descends because it preserves the
linear commutator span. Rank balance is an additive identity in that module;
it is not an integral or group-cohomological torsion theorem.
-/

noncomputable section

namespace InfoGeometry.Geometry.AssociativeGaugeConnection

variable {R A n : Type*} [Ring R] [Ring A] [Module R A]
  [Fintype n] [DecidableEq n]

/-- Entrywise application preserves the associative Leibniz law. -/
theorem IsLeibniz.mapMatrix {D : Module.End R A} (hD : IsLeibniz D) :
    IsLeibniz (D.mapMatrix : Module.End R (Matrix n n A)) := by
  intro X Y
  ext i j
  change D (∑ k, X i k * Y k j) =
    (∑ k, D (X i k) * Y k j) + ∑ k, X i k * D (Y k j)
  rw [map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact hD (X i k) (Y k j)

omit [Fintype n] [DecidableEq n] in
theorem mapMatrix_commute (D E : Module.End R A)
    (h : ∀ x, D (E x) = E (D x)) (X : Matrix n n A) :
    D.mapMatrix (E.mapMatrix X) = E.mapMatrix (D.mapMatrix X) := by
  ext i j
  exact h (X i j)

omit [DecidableEq n] in
theorem trace_mapMatrix (D : Module.End R A) (X : Matrix n n A) :
    Matrix.trace (D.mapMatrix X) = D (Matrix.trace X) := by
  change (∑ i, D (X i i)) = D (∑ i, X i i)
  simp only [map_sum]

/-- The commutator trace cannot be discarded over a general coefficient ring. -/
theorem trace_curvature (D E : Module.End R A) (X Y : Matrix n n A) :
    Matrix.trace (curvature D.mapMatrix E.mapMatrix X Y) =
      D (Matrix.trace Y) - E (Matrix.trace X) + Matrix.trace (X * Y - Y * X) := by
  simp only [curvature, Matrix.trace_sub, Matrix.trace_add, trace_mapMatrix]
  abel

theorem trace_correctedCurvature (D E : Module.End R A) (X Y : Matrix n n A)
    (c : A) :
    Matrix.trace (curvature D.mapMatrix E.mapMatrix X Y +
      Matrix.diagonal (fun _ : n => c)) =
      D (Matrix.trace Y) - E (Matrix.trace X) + Matrix.trace (X * Y - Y * X) +
        Fintype.card n • c := by
  rw [Matrix.trace_add, trace_curvature, Matrix.trace_diagonal]
  simp

/-- Corrected flatness gives this exact raw coefficient identity. -/
theorem rank_nsmul_eq_of_correctedFlat (D E : Module.End R A) (X Y : Matrix n n A)
    (c : A)
    (h : curvature D.mapMatrix E.mapMatrix X Y + Matrix.diagonal (fun _ : n => c) = 0) :
    Fintype.card n • c =
      -(D (Matrix.trace Y) - E (Matrix.trace X) + Matrix.trace (X * Y - Y * X)) := by
  have ht := congrArg Matrix.trace h
  rw [trace_correctedCurvature, Matrix.trace_zero] at ht
  exact eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using ht)

end InfoGeometry.Geometry.AssociativeGaugeConnection

namespace InfoGeometry.Algebra.CyclicMatrixCurvature

open InfoGeometry.Geometry.AssociativeGaugeConnection

variable {R A : Type*} [Ring R] [Ring A] [Module R A]

/-- A derivation sends a commutator to a sum of two commutators. -/
theorem cyclicClass_derivative_commutator (D : Module.End R A) (hD : IsLeibniz D)
    (a b : A) : cyclicClass R A (D (a * b - b * a)) = 0 := by
  have heq : D (a * b - b * a) =
      (D a * b - b * D a) + (a * D b - D b * a) := by
    rw [map_sub, hD, hD]
    noncomm_ring
  rw [heq, map_add, cyclicClass_commutator, cyclicClass_commutator, add_zero]

theorem commutatorSpan_le_ker_derivative (D : Module.End R A) (hD : IsLeibniz D) :
    commutatorSpan R A ≤ LinearMap.ker ((cyclicClass R A).comp D) := by
  apply Submodule.span_le.mpr
  rintro x ⟨a, b, rfl⟩
  exact cyclicClass_derivative_commutator D hD a b

/-- The native quotient lift on the already owned cyclic coefficient module. -/
def cyclicDerivative (D : Module.End R A) (hD : IsLeibniz D) :
    Module.End R (CyclicModule R A) :=
  (commutatorSpan R A).liftQ ((cyclicClass R A).comp D)
    (commutatorSpan_le_ker_derivative D hD)

@[simp]
theorem cyclicDerivative_class (D : Module.End R A) (hD : IsLeibniz D) (a : A) :
    cyclicDerivative D hD (cyclicClass R A a) = cyclicClass R A (D a) := rfl

theorem cyclicDerivative_commute (D E : Module.End R A)
    (hD : IsLeibniz D) (hE : IsLeibniz E)
    (hcomm : ∀ x, D (E x) = E (D x)) (x : CyclicModule R A) :
    cyclicDerivative D hD (cyclicDerivative E hE x) =
      cyclicDerivative E hE (cyclicDerivative D hD x) := by
  obtain ⟨a, rfl⟩ := (commutatorSpan R A).mkQ_surjective x
  change cyclicClass R A (D (E a)) = cyclicClass R A (E (D a))
  rw [hcomm]

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem cyclicTrace_mapMatrix (D : Module.End R A) (hD : IsLeibniz D)
    (X : Matrix n n A) :
    cyclicTrace R A (D.mapMatrix X) = cyclicDerivative D hD (cyclicTrace R A X) := by
  change cyclicClass R A (Matrix.trace (D.mapMatrix X)) =
    cyclicDerivative D hD (cyclicClass R A (Matrix.trace X))
  rw [trace_mapMatrix, cyclicDerivative_class]

/-- The commutator cancels only after passing to the cyclic quotient. -/
theorem cyclicTrace_curvature (D E : Module.End R A)
    (hD : IsLeibniz D) (hE : IsLeibniz E) (X Y : Matrix n n A) :
    cyclicTrace R A (curvature D.mapMatrix E.mapMatrix X Y) =
      cyclicDerivative D hD (cyclicTrace R A Y) -
        cyclicDerivative E hE (cyclicTrace R A X) := by
  have heq : curvature D.mapMatrix E.mapMatrix X Y =
      D.mapMatrix Y - E.mapMatrix X + (X * Y - Y * X) := by
    unfold curvature
    abel
  rw [heq, map_add, map_sub, cyclicTrace_commutator, add_zero,
    cyclicTrace_mapMatrix D hD, cyclicTrace_mapMatrix E hE]

theorem cyclic_rank_balance_of_correctedFlat (D E : Module.End R A)
    (hD : IsLeibniz D) (hE : IsLeibniz E) (X Y : Matrix n n A) (c : A)
    (h : curvature D.mapMatrix E.mapMatrix X Y + Matrix.diagonal (fun _ : n => c) = 0) :
    Fintype.card n • cyclicClass R A c =
      -(cyclicDerivative D hD (cyclicTrace R A Y) -
        cyclicDerivative E hE (cyclicTrace R A X)) := by
  have ht := congrArg (cyclicTrace R A) h
  rw [map_add, cyclicTrace_curvature D E hD hE, cyclicTrace_diagonal, map_zero] at ht
  rw [Nat.cast_smul_eq_nsmul] at ht
  exact eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using ht)

end InfoGeometry.Algebra.CyclicMatrixCurvature

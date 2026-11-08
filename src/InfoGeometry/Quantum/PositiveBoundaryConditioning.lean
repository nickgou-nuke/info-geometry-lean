/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.KrausBoundaryDuality
import Mathlib.Analysis.Matrix.Order

/-!
# Positive conditioning on the full matrix algebra

The operation is specified as the square-root sandwich `sqrt E * X * sqrt E`.
It is not identified with a classical pointwise product, a unique posterior,
or the different sandwich `sqrt X * E * sqrt X`.
-/

noncomputable section
namespace InfoGeometry.Quantum.BoundaryConditioning

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- A specified positive update, with the effect on the outside. -/
def sandwich (X E : Matrix n n ℂ) : Matrix n n ℂ :=
  CFC.sqrt E * X * CFC.sqrt E

/-- The update preserves positivity without assuming `X` and `E` commute. -/
theorem sandwich_posSemidef {X : Matrix n n ℂ} (hX : X.PosSemidef)
    (E : Matrix n n ℂ) : (sandwich X E).PosSemidef := by
  have hs := (CFC.sqrt_nonneg E).posSemidef.isHermitian
  simpa only [sandwich, hs.eq] using hX.mul_mul_conjTranspose_same (CFC.sqrt E)

/-- The operator update has precisely the boundary pairing as its trace. -/
theorem trace_sandwich (X : Matrix n n ℂ) {E : Matrix n n ℂ}
    (hE : E.PosSemidef) : trace (sandwich X E) = trace (X * E) := by
  unfold sandwich
  rw [trace_mul_cycle, CFC.sqrt_mul_sqrt_self E hE.nonneg, trace_mul_comm]

/-- Positive boundary operators have a nonnegative real trace pairing. -/
theorem trace_pairing_nonneg {X E : Matrix n n ℂ}
    (hX : X.PosSemidef) (hE : E.PosSemidef) : 0 ≤ trace (X * E) := by
  rw [← trace_sandwich X hE]
  exact (sandwich_posSemidef hX E).trace_nonneg

/-- The two sandwich orders have the same trace; no equality of operators is asserted. -/
theorem trace_sandwich_swap {X E : Matrix n n ℂ}
    (hX : X.PosSemidef) (hE : E.PosSemidef) :
    trace (sandwich X E) = trace (sandwich E X) := by
  rw [trace_sandwich X hE, trace_sandwich E hX, trace_mul_comm]

/-- Normalization by the real boundary weight. Theorems require positive weight. -/
def conditioned (X E : Matrix n n ℂ) : Matrix n n ℂ :=
  ((trace (X * E)).re)⁻¹ • sandwich X E

theorem conditioned_posSemidef {X E : Matrix n n ℂ} (hX : X.PosSemidef)
    (hweight : 0 < (trace (X * E)).re) : (conditioned X E).PosSemidef := by
  exact (sandwich_posSemidef hX E).smul (inv_nonneg.mpr hweight.le)

/-- Positive boundary weight excludes zero normalization, including the empty
matrix carrier. -/
theorem trace_conditioned {X E : Matrix n n ℂ}
    (hX : X.PosSemidef) (hE : E.PosSemidef)
    (hweight : 0 < (trace (X * E)).re) : trace (conditioned X E) = 1 := by
  have him : (trace (X * E)).im = 0 :=
    (Complex.nonneg_iff.mp (trace_pairing_nonneg hX hE)).2.symm
  have hreal : ((trace (X * E)).re : ℂ) = trace (X * E) := by
    apply Complex.ext <;> simp [him]
  rw [conditioned, trace_smul, trace_sandwich X hE, ← hreal]
  simp [Complex.real_smul, ← Complex.ofReal_mul, ne_of_gt hweight]

/-- The naive product of Hermitian boundary operators is Hermitian exactly
when they commute. This identifies the obstruction, rather than imposing it. -/
theorem product_isHermitian_iff {X E : Matrix n n ℂ}
    (hX : X.IsHermitian) (hE : E.IsHermitian) :
    (X * E).IsHermitian ↔ X * E = E * X := by
  simp only [Matrix.IsHermitian, conjTranspose_mul, hX.eq, hE.eq, eq_comm]

/-- The native Loewner partial order is preserved by a Kraus map. -/
theorem krausMap_monotone [Fintype ι] [DecidableEq ι] (V : ι → Matrix n n ℂ) :
    Monotone (Choi.krausMap V) := by
  intro X Y hXY
  rw [Matrix.le_iff, ← map_sub]
  exact Choi.krausMap_posSemidef V (Matrix.le_iff.mp hXY)

/-- The specified conditioning numerator is monotone in the input operator. -/
theorem sandwich_monotone (E : Matrix n n ℂ) : Monotone (fun X => sandwich X E) := by
  intro X Y hXY
  rw [Matrix.le_iff]
  have h := sandwich_posSemidef (Matrix.le_iff.mp hXY) E
  simpa only [sandwich, mul_sub, sub_mul] using h

end InfoGeometry.Quantum.BoundaryConditioning

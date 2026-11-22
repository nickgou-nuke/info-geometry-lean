/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.AlbertCayleyDickson
import Mathlib.Tactic

/-!
# A noncommutative operator counterexample to the associator Filippov identity

This witness uses the repository's `OpZornMatrix` multiplication over the
genuinely noncommutative coefficient operator ring `M₂(ℤ)`. It records the
exact defect for five explicit operator-valued inputs; it makes no claim about
the standard Malcev identity of the commutator bracket.
-/

namespace InfoGeometry.NCG.ZornAssociatorFilippovCounterexample

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.OpZornMatrix

abbrev CoefficientOperator := Matrix (Fin 2) (Fin 2) ℤ

/-- The diagonal matrix unit `E₁₁` in the coefficient operator ring. -/
def e11 : CoefficientOperator := !![1, 0; 0, 0]

/-- The lower matrix unit `E₂₁` in the coefficient operator ring. -/
def e21 : CoefficientOperator := !![0, 0; 1, 0]

/-- The upper matrix unit `E₁₂` in the coefficient operator ring. -/
def e12 : CoefficientOperator := !![0, 1; 0, 0]

/-- A diagonal Zorn operator with noncentral matrix-operator entries. -/
def H : OpZornMatrix CoefficientOperator := ⟨e11, 0, 0, e11⟩

/-- Upper Zorn operator supported in the first vector channel. -/
def upperX (c : CoefficientOperator) : OpZornMatrix CoefficientOperator :=
  ⟨0, ⟨c, 0, 0⟩, 0, 0⟩

/-- Upper Zorn operator supported in the second vector channel. -/
def upperY (c : CoefficientOperator) : OpZornMatrix CoefficientOperator :=
  ⟨0, ⟨0, c, 0⟩, 0, 0⟩

/-- Lower Zorn operator supported in the first vector channel. -/
def lowerX (c : CoefficientOperator) : OpZornMatrix CoefficientOperator :=
  ⟨0, 0, ⟨c, 0, 0⟩, 0⟩

/-- Left minus right defect of the ternary Filippov identity for the native
Zorn associator. -/
def associatorFilippovDefect
    (x y u v w : OpZornMatrix CoefficientOperator) : OpZornMatrix CoefficientOperator :=
  opAssociator x y (opAssociator u v w) -
    (opAssociator (opAssociator x y u) v w +
      opAssociator u (opAssociator x y v) w +
      opAssociator u v (opAssociator x y w))

/-- The coefficient matrix units used in the witness do not commute. -/
theorem coefficient_units_noncommute : e11 * e21 ≠ e21 * e11 := by
  decide

/-- Exact nonzero channel component of the Filippov defect on the five
operator-valued inputs. -/
theorem associatorFilippovDefect_component :
    (associatorFilippovDefect H (upperX e11) H (upperY e21) (lowerX e12)).v.y =
      !![-1, 0; 0, 0] := by
  decide

/-- The native Zorn associator on this noncommutative matrix-operator carrier
fails the ternary Filippov fundamental identity. -/
theorem associator_not_filippov_on_matrix_operators :
    associatorFilippovDefect H (upperX e11) H (upperY e21) (lowerX e12) ≠ 0 := by
  intro h
  have hcoord := congrArg (fun X : OpZornMatrix CoefficientOperator => X.v.y) h
  rw [associatorFilippovDefect_component] at hcoord
  have h00 := congrArg (fun M : CoefficientOperator => M 0 0) hcoord
  norm_num at h00

end InfoGeometry.NCG.ZornAssociatorFilippovCounterexample

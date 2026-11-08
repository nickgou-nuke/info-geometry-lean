/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.LieJordanGenerators
import InfoGeometry.Core.PeirceSandwichDuality
import InfoGeometry.Modular.GKSLDissipatorAlgebraic

/-!
# Ordinary and reflection-weighted trace of three distinct generators

All trace identities act on full matrix algebras. Only the weighted column
requires opposite Peirce corners. Trace annihilation of a generator is
distinct from trace preservation of a map. The final bridges use the existing
Heisenberg-oriented dissipator with real transpose pairing.
-/

namespace InfoGeometry.Canonical.LieJordanGeneratorTrace

open Matrix Core.PeirceDecomposition Core.PeirceGrading Core.PeirceCoupledCorners
open Core.PeirceSandwichDuality Core.LieJordanGenerators LieJordanSandwichGeometry

attribute [local instance 100] LieRing.ofAssociativeRing

section Trace

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

theorem trace_sandwich_sub (u v x : Matrix n n R) :
    trace (u * x * v - v * x * u) = -trace (⁅u, v⁆ * x) := by
  change trace (u * x * v - v * x * u) = -trace ((u * v - v * u) * x)
  rw [trace_sub, sub_mul, trace_sub,
    trace_mul_comm (u * x) v, trace_mul_comm (v * x) u]
  simp only [← mul_assoc]
  abel

theorem trace_symmetricGenerator (u v x : Matrix n n R) :
    trace (symmetricGenerator (R := R) u v x) = 0 := by
  rw [symmetricGenerator_sandwich_apply, two_nsmul, trace_sub, trace_add,
    trace_sandwich_sum, trace_add, trace_mul_comm x (u * v + v * u)]
  abel

theorem trace_skewPlusGenerator (u v x : Matrix n n R) :
    trace (skewPlusGenerator (R := R) u v x) = 0 := by
  rw [skewPlusGenerator_sandwich_apply, two_nsmul, trace_add, trace_add,
    trace_sandwich_sub, trace_add, trace_mul_comm x ⁅u, v⁆]
  abel

theorem trace_skewMinusGenerator (u v x : Matrix n n R) :
    trace (skewMinusGenerator (R := R) u v x) = -(4 • trace (⁅u, v⁆ * x)) := by
  rw [skewMinusGenerator_sandwich_apply, two_nsmul, trace_sub, trace_add,
    trace_sandwich_sub, trace_add, trace_mul_comm x ⁅u, v⁆]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

theorem trace_comp_symmetricGenerator (u v : Matrix n n R) :
    (traceLinearMap n R R).comp (symmetricGenerator (R := R) u v) = 0 := by
  ext x
  exact trace_symmetricGenerator u v x

theorem trace_comp_skewPlusGenerator (u v : Matrix n n R) :
    (traceLinearMap n R R).comp (skewPlusGenerator (R := R) u v) = 0 := by
  ext x
  exact trace_skewPlusGenerator u v x

theorem trace_weighted_jordan_of_commute (g a x : Matrix n n R) (h : Commute g a) :
    trace (g * (a * x + x * a)) = 2 • trace ((g * a) * x) := by
  rw [mul_add, trace_add, ← mul_assoc g a x]
  have hc : trace (g * (x * a)) = trace ((g * a) * x) := by
    rw [← mul_assoc, trace_mul_comm (g * x) a, ← mul_assoc, h.eq]
  rw [hc, two_nsmul]

variable {p u v : Matrix n n R}

theorem trace_reflection_sandwich_sum (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) (x : Matrix n n R) :
    trace (reflection p * (u * x * v + v * x * u)) = -trace (⁅u, v⁆ * x) := by
  rw [reflection_mul_sandwich_sum hp hu hv, trace_sandwich_sub]

theorem trace_reflection_sandwich_sub (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) (x : Matrix n n R) :
    trace (reflection p * (u * x * v - v * x * u)) =
      trace ((u * v + v * u) * x) := by
  rw [reflection_mul_sandwich_sub hp hu hv, trace_sandwich_sum]

theorem trace_reflection_symmetricGenerator (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) (x : Matrix n n R) :
    trace (reflection p * symmetricGenerator (R := R) u v x) =
      -(4 • trace (⁅u, v⁆ * x)) := by
  rw [symmetricGenerator_sandwich_apply, two_nsmul, mul_sub, mul_add,
    trace_sub, trace_add, trace_reflection_sandwich_sum hp hu hv,
    trace_weighted_jordan_of_commute _ _ _
      (even_commutes_reflection hp (jordan_mem_even hp hu hv)),
    reflection_mul_jordan hp hu hv]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

theorem trace_reflection_skewMinusGenerator (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) (x : Matrix n n R) :
    trace (reflection p * skewMinusGenerator (R := R) u v x) = 0 := by
  rw [skewMinusGenerator_sandwich_apply, two_nsmul, mul_sub, mul_add,
    trace_sub, trace_add, trace_reflection_sandwich_sub hp hu hv,
    trace_weighted_jordan_of_commute _ _ _
      (even_commutes_reflection hp (bracket_mem_even hp hu hv)),
    reflection_mul_bracket hp hu hv, two_nsmul]
  abel

theorem trace_reflection_skewPlusGenerator (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) (x : Matrix n n R) :
    trace (reflection p * skewPlusGenerator (R := R) u v x) =
      4 • trace ((u * v + v * u) * x) := by
  rw [skewPlusGenerator_sandwich_apply, two_nsmul, mul_add, mul_add,
    trace_add, trace_add, trace_reflection_sandwich_sub hp hu hv,
    trace_weighted_jordan_of_commute _ _ _
      (even_commutes_reflection hp (bracket_mem_even hp hu hv)),
    reflection_mul_bracket hp hu hv]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

theorem weighted_trace_comp_skewMinusGenerator (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    ((traceLinearMap n R R).comp (LinearMap.mulLeft R (reflection p))).comp
      (skewMinusGenerator (R := R) u v) = 0 := by
  ext x
  exact trace_reflection_skewMinusGenerator hp hu hv x

end Trace

section RealDissipator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The existing jump owner has Heisenberg orientation; the pair gives the symmetric generator. -/
theorem symmetricGenerator_eq_dissipator_pair (u x : Matrix n n ℝ) :
    symmetricGenerator (R := ℝ) u u.transpose x =
      2 • (Modular.GKSL.dissipatorTerm ((1 / 2 : ℝ) • 1) u x +
        Modular.GKSL.dissipatorTerm ((1 / 2 : ℝ) • 1) u.transpose x) := by
  rw [symmetricGenerator_sandwich_apply]
  simp only [Modular.GKSL.dissipatorTerm, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
    smul_mul_assoc, one_mul, add_mul, mul_add, mul_assoc, two_nsmul]
  module

/-- A signed difference gives the unit-annihilating skew generator, with this exact orientation. -/
theorem skewMinusGenerator_eq_dissipator_difference (u x : Matrix n n ℝ) :
    skewMinusGenerator (R := ℝ) u u.transpose x =
      2 • (Modular.GKSL.dissipatorTerm ((1 / 2 : ℝ) • 1) u.transpose x -
        Modular.GKSL.dissipatorTerm ((1 / 2 : ℝ) • 1) u x) := by
  rw [skewMinusGenerator_sandwich_apply]
  simp only [Modular.GKSL.dissipatorTerm, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
    Ring.lie_def, smul_mul_assoc, one_mul, sub_mul, mul_sub, mul_assoc, two_nsmul]
  module

end RealDissipator

end InfoGeometry.Canonical.LieJordanGeneratorTrace

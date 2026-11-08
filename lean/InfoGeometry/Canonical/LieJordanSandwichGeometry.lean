/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCoupledCorners
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

/-!
# Trace, parity and positivity of two-sided matrix multiplication

The two-sided maps are Mathlib's native `LinearMap.mulLeftRight`.
Trace transport holds for arbitrary matrix inputs. Adjoint pairing supplies
positive-semidefinite preservation; trace preservation has the separate exact
normalization condition `u * v + v * u = 1`.
-/

namespace InfoGeometry.Canonical.LieJordanSandwichGeometry

open Core.PeirceDecomposition Core.PeirceGrading Core.PeirceCoupledCorners

section Parity

variable {A : Type*} [Ring A] {p u v x : A}

/-- Opposite corners send every input into the existing even Peirce sector. -/
theorem sandwich_sum_mem_even (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) (x : A) :
    u * x * v + v * x * u ∈ LinearMap.range (even p) := by
  rw [mem_even_iff hp]
  calc
    p * (u * x * v + v * x * u) =
        (p * u) * x * v + (p * v) * x * u := by noncomm_ring
    _ = u * x * v := by
      rw [left_support10 hp hu, left_support01 hp hv]
      simp
    _ = (u * x * v + v * x * u) * p := by
      rw [add_mul, mul_assoc (u * x) v p, right_support01 hp hv,
        mul_assoc (v * x) u p, right_support10 hp hu, mul_zero, add_zero]

/-- Actual odd membership, rather than a parity label, annihilates both sandwiches. -/
theorem sandwich_sum_eq_zero_of_odd (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p)
    (hx : x ∈ LinearMap.range (odd p)) : u * x * v + v * x * u = 0 := by
  have hsplit := (mem_odd_iff hp).mp hx
  have huv : u * x * v = 0 := by
    calc
      u * x * v = u * (p * x + x * p) * v := by rw [hsplit]
      _ = (u * p) * x * v + u * x * (p * v) := by noncomm_ring
      _ = 0 := by rw [right_support10 hp hu, left_support01 hp hv]; simp
  have hvu : v * x * u = 0 := by
    have h := congrArg (fun y : A => v * y * u) hsplit
    have he : v * (p * x + x * p) * u = v * x * u + v * x * u := by
      calc
        _ = (v * p) * x * u + v * x * (p * u) := by noncomm_ring
        _ = _ := by rw [right_support01 hp hv, left_support10 hp hu]
    rw [he] at h
    exact add_left_cancel (h.trans (add_zero (v * x * u)).symm)
  rw [huv, hvu, add_zero]

/-- The whole odd projection is in the kernel of the native sandwich endomorphism. -/
theorem sandwich_comp_odd_eq_zero (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (LinearMap.mulLeftRight ℤ (u, v) + LinearMap.mulLeftRight ℤ (v, u)) *
      odd p = 0 := by
  ext x
  exact sandwich_sum_eq_zero_of_odd hp hu hv ⟨x, rfl⟩

end Parity

section Trace

variable {R n : Type*} [CommRing R] [Fintype n]

/-- Cyclicity gives the trace transport identity for every full matrix. -/
theorem trace_sandwich_sum (u v x : Matrix n n R) :
    Matrix.trace (u * x * v + v * x * u) =
      Matrix.trace ((u * v + v * u) * x) := by
  rw [Matrix.trace_add, add_mul, Matrix.trace_add]
  have huv : Matrix.trace (u * x * v) = Matrix.trace (v * u * x) := by
    rw [Matrix.trace_mul_comm (u * x) v, ← mul_assoc]
  have hvu : Matrix.trace (v * x * u) = Matrix.trace (u * v * x) := by
    rw [Matrix.trace_mul_comm (v * x) u, ← mul_assoc]
  rw [huv, hvu, add_comm]

theorem sandwich_sum_one [DecidableEq n] (u v : Matrix n n R) :
    u * 1 * v + v * 1 * u = u * v + v * u := by
  simp only [mul_one]

/-- Trace preservation on all matrices has an exact normalization criterion. -/
theorem trace_preserving_iff [DecidableEq n] (u v : Matrix n n R) :
    (∀ x : Matrix n n R,
      Matrix.trace (u * x * v + v * x * u) = Matrix.trace x) ↔
        u * v + v * u = 1 := by
  constructor
  · intro h
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro x
    simpa only [trace_sandwich_sum, one_mul] using h x
  · intro h x
    rw [trace_sandwich_sum, h, one_mul]

end Trace

section Positivity

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n]

/-- Adjoint pairing gives positive-semidefinite preservation on full matrices. -/
theorem adjoint_sandwich_sum_posSemidef (u : Matrix n n ℂ)
    {x : Matrix n n ℂ} (hx : x.PosSemidef) :
    (u * x * uᴴ + uᴴ * x * u).PosSemidef :=
  (hx.mul_mul_conjTranspose_same u).add (hx.conjTranspose_mul_mul_same u)

end Positivity

end InfoGeometry.Canonical.LieJordanSandwichGeometry

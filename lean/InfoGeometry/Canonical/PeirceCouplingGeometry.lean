/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCoupledCorners
import InfoGeometry.Core.PeirceMatrixTracePairing
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Trace and kernel geometry of opposite Peirce corners

The two directed corners are independent elements of the existing Peirce
sectors. Their trace balances and kernel decompositions hold over an arbitrary
commutative coefficient ring. Opposite-corner separation supplies a partner
with nonzero coupling for each nonzero corner; no assertion about every
possible partner or about positivity is made here.
-/

namespace InfoGeometry.Canonical.PeirceCouplingGeometry

open Matrix
open Core.PeirceDecomposition Core.PeirceGrading Core.PeirceCoupledCorners

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
variable {p u v : Matrix n n R}

/-- A directed corner has zero trace by cyclicity and its support equations. -/
theorem trace_eq_zero_of_mem_peirce10 (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) : trace u = 0 := by
  calc
    trace u = trace (p * u) := congrArg trace (left_support10 hp hu).symm
    _ = trace (u * p) := trace_mul_comm _ _
    _ = 0 := by rw [right_support10 hp hu, trace_zero]

/-- The opposite directed corner also has zero trace. -/
theorem trace_eq_zero_of_mem_peirce01 (hp : IsIdempotentElem p)
    (hv : v ∈ peirce01 p) : trace v = 0 := by
  calc
    trace v = trace (v * p) := congrArg trace (right_support01 hp hv).symm
    _ = trace (p * v) := trace_mul_comm _ _
    _ = 0 := by rw [left_support01 hp hv, trace_zero]

theorem trace_coupled (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) : trace (u + v) = 0 := by
  rw [trace_add, trace_eq_zero_of_mem_peirce10 hp hu,
    trace_eq_zero_of_mem_peirce01 hp hv, add_zero]

omit [DecidableEq n] in
/-- Cyclicity doubles the trace of either ordered product. -/
theorem trace_jordan (u v : Matrix n n R) :
    trace (u * v + v * u) = 2 * trace (u * v) := by
  rw [trace_add, trace_mul_comm v u, two_mul]

theorem trace_coupled_square (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    trace ((u + v) ^ 2) = 2 * trace (u * v) := by
  rw [coupled_square hp hu hv]
  exact trace_jordan u v

/-- The two quadratic compressions have equal trace. -/
theorem trace_jordan_compressions (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    trace (p * (u * v + v * u) * p) =
      trace ((1 - p) * (u * v + v * u) * (1 - p)) := by
  change trace (component11 p (u * v + v * u)) =
    trace (component00 p (u * v + v * u))
  rw [component11_jordan hp hu hv, component00_jordan hp hu hv]
  exact trace_mul_comm _ _

/-- The two compressed native brackets have cancelling traces. -/
theorem trace_bracket_compressions (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    trace (p * ⁅u, v⁆ * p) +
      trace ((1 - p) * ⁅u, v⁆ * (1 - p)) = 0 := by
  change trace (component11 p ⁅u, v⁆) + trace (component00 p ⁅u, v⁆) = 0
  rw [component11_bracket hp hu hv, component00_bracket hp hu hv,
    trace_neg, trace_mul_comm u v, add_neg_cancel]

/-- Reflection turns the symmetric product into a traceless native bracket. -/
theorem trace_reflection_mul_jordan (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    trace (reflection p * (u * v + v * u)) = 0 := by
  rw [reflection_mul_jordan hp hu hv]
  exact LieAlgebra.matrix_trace_commutator_zero n R u v

/-- The reflected bracket has the trace of the symmetric product. -/
theorem trace_reflection_mul_bracket (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    trace (reflection p * ⁅u, v⁆) = trace (u * v + v * u) := by
  rw [reflection_mul_bracket hp hu hv]

theorem trace_reflection_mul_bracket_eq_two (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    trace (reflection p * ⁅u, v⁆) = 2 * trace (u * v) := by
  rw [trace_reflection_mul_bracket hp hu hv, trace_jordan]

/-- Every nonzero directed corner is detected by some opposite corner. -/
theorem exists_opposite_trace_partner (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hu0 : u ≠ 0) :
    ∃ v : Matrix n n R, v ∈ peirce01 p ∧ trace (u * v) ≠ 0 := by
  classical
  by_contra h
  apply hu0
  apply component10_eq_zero_of_trace_pairing p u (component10_fixed hp hu)
  intro a
  by_contra ha
  exact h ⟨component01 p a, component01_mem p a, ha⟩

/-- A detecting partner gives a nonzero coupled square, also in characteristic two.

The proof extracts an ordered product from the square; it does not cancel the
factor two in its trace.
-/
theorem exists_opposite_nonzero_coupled_square (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hu0 : u ≠ 0) :
    ∃ v : Matrix n n R, v ∈ peirce01 p ∧ v ≠ 0 ∧ (u + v) ^ 2 ≠ 0 := by
  obtain ⟨v, hv, ht⟩ := exists_opposite_trace_partner hp hu hu0
  refine ⟨v, hv, ?_, ?_⟩
  · intro hv0
    apply ht
    rw [hv0, mul_zero, trace_zero]
  · intro hs
    have hk : u * v + v * u = 0 := by
      rw [← coupled_square hp hu hv]
      exact hs
    have huv : u * v = 0 := ((jordan_eq_zero_iff_products hp hu hv).mp hk).1
    apply ht
    rw [huv, trace_zero]

/-- Opposite output supports prevent cancellation in the coupled kernel. -/
theorem coupled_kernel (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    LinearMap.ker (u + v).mulVecLin =
      LinearMap.ker u.mulVecLin ⊓ LinearMap.ker v.mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_inf, Matrix.mulVecLin_apply]
  constructor
  · intro hx
    have hux : u *ᵥ x = 0 := by
      have h := congrArg (fun y => p *ᵥ y) hx
      simpa only [Matrix.mulVec_mulVec, mul_add, left_support10 hp hu,
        left_support01 hp hv, add_zero, Matrix.mulVec_zero] using h
    refine ⟨hux, ?_⟩
    simpa only [Matrix.add_mulVec, hux, zero_add] using hx
  · rintro ⟨hux, hvx⟩
    rw [Matrix.add_mulVec, hux, hvx, add_zero]

/-- Reflection identifies the zero modes of the symmetric product and bracket. -/
theorem jordan_kernel_eq_bracket_kernel (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    LinearMap.ker (u * v + v * u).mulVecLin =
      LinearMap.ker (⁅u, v⁆).mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hx
    rw [← reflection_mul_jordan hp hu hv, ← Matrix.mulVec_mulVec,
      hx, Matrix.mulVec_zero]
  · intro hx
    rw [← reflection_mul_bracket hp hu hv, ← Matrix.mulVec_mulVec,
      hx, Matrix.mulVec_zero]

end InfoGeometry.Canonical.PeirceCouplingGeometry

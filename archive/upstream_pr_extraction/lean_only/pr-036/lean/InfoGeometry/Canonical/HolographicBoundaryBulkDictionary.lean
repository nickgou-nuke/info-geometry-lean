import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.HolographicBoundaryBulkDictionary

A minimal algebraic boundary-to-bulk dictionary surface.

This file only defines a small real-coordinate model together with two elementary
kernel-checked theorems. It does not claim a full AdS/CFT correspondence,
geometric completeness, or physical closure beyond the stated algebraic facts.
-/

namespace InfoGeometry.Canonical.HolographicBoundaryBulkDictionary

set_option autoImplicit false

/-- Monomial boundary datum carrying a coefficient and exponent. -/
structure Monomial where
  coeff : ℝ
  exp : ℝ

/-- A three-coordinate bulk state used for the local algebraic dictionary. -/
structure SymmState2x2 (R : Type*) [CommRing R] where
  t : R
  x : R
  z : R

/-- The doubled temporal readout. -/
def trace_2x2 {R : Type*} [CommRing R] (S : SymmState2x2 R) : R :=
  S.t + S.t

/-- The quadratic bulk interval readout. -/
def det_2x2 {R : Type*} [CommRing R] (S : SymmState2x2 R) : R :=
  S.t * S.t - S.x * S.x - S.z * S.z

/--
A direct boundary-to-bulk coordinate map used by this local algebraic model.
-/
def holographic_map (M : Monomial) : SymmState2x2 ℝ :=
  ⟨M.coeff, M.exp, 0⟩

/-- The map reads the boundary coefficient as the doubled bulk trace. -/
theorem holographic_trace_isomorphism (M : Monomial) :
    trace_2x2 (holographic_map M) = 2 * M.coeff := by
  unfold trace_2x2 holographic_map
  ring

/--
If both boundary coordinates vanish, then the mapped bulk state has zero
quadratic interval.
-/
theorem boundary_nullcone_of_zero_boundary_data
    (M : Monomial) (hcoeff : M.coeff = 0) (hexp : M.exp = 0) :
    det_2x2 (holographic_map M) = 0 := by
  unfold det_2x2 holographic_map
  rw [hcoeff, hexp]
  ring

/-- Exact interval readout for the local holographic map. -/
theorem holographic_det_formula (M : Monomial) :
    det_2x2 (holographic_map M) = M.coeff ^ 2 - M.exp ^ 2 := by
  unfold det_2x2 holographic_map
  ring

end InfoGeometry.Canonical.HolographicBoundaryBulkDictionary

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.RiemannHypothesisHalfPlaneReduction
import New.Main

/-!
# The pinned Dirichlet GRH proof at the native half-plane interface

This module belongs to the isolated Lean 4.35 integration package.  `New.grh`
comes from the readable edition of `lsernau/grh-lean` at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.  Its statement uses Mathlib's
`DirichletCharacter.LFunction` and is definitionally the native repository's
`DirichletRightHalfPlaneNonvanishing` predicate.

The imported proof discharges that existing predicate.  The Riemann hypothesis
below then follows through the repository's existing reduction, without an
additional nonvanishing or zero-location hypothesis.  The complex arithmetic
boundary is kept in this optional integration module.
-/

namespace InfoGeometry.GRHIntegration

open InfoGeometry.Arithmetic.RiemannHypothesisHalfPlaneReduction

/-- The pinned external proof supplies the native Dirichlet half-plane
nonvanishing predicate, including the principal-character pole exception. -/
theorem dirichletRightHalfPlaneNonvanishing : DirichletRightHalfPlaneNonvanishing :=
  New.grh

/-- The native zeta half-plane statement is the modulus-one specialization of
the proved Dirichlet statement. -/
theorem zetaRightHalfPlaneNonvanishing : ZetaRightHalfPlaneNonvanishing :=
  zetaRightHalfPlane_of_dirichletRightHalfPlane dirichletRightHalfPlaneNonvanishing

/-- The existing native half-plane reduction, now supplied by the pinned
external proof rather than a hypothesis. -/
theorem riemannHypothesis : _root_.RiemannHypothesis :=
  riemannHypothesis_of_dirichletRightHalfPlane dirichletRightHalfPlaneNonvanishing

/-- For every positive modulus and every Dirichlet character, an actual
Mathlib L-function zero in the critical strip has real part `1 / 2`. -/
theorem dirichletL_zeros_on_line (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs_pos : 0 < s.re) (hs_lt : s.re < 1)
    (hs_zero : DirichletCharacter.LFunction χ s = 0) : s.re = 1 / 2 :=
  New.zeros_on_line dirichletRightHalfPlaneNonvanishing N χ s hs_pos hs_lt hs_zero

end InfoGeometry.GRHIntegration

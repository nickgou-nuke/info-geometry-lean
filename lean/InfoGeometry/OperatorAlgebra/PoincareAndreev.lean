/-
InfoGeometry/OperatorAlgebra/PoincareAndreev.lean

Poincare-Andreev boundary carrier.

Below-gap no-leakage behavior is supplied as an interface law. This module does
not infer perfect Andreev reflection from `epsilon < Δ` alone.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.AndreevBoundary

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PoincareAndreev

open InfoGeometry.OperatorAlgebra.AndreevBoundary

/--
Poincare-Andreev boundary carrier.

This packages a projective/conformal boundary together with an Andreev boundary
and a superconducting gap.
-/
structure PoincareAndreevBoundary
    (V : Type*) [AddCommGroup V] [Module ℝ V] where
  boundary :
    AndreevBoundaryDatum V

  gapDelta :
    ℝ

  gap_pos :
    0 < gapDelta

  /-- Reflection efficiency readout. -/
  reflectionEfficiency :
    ℝ → ℝ

  /-- Transmission/leakage readout. -/
  leakage :
    ℝ → ℝ

  /--
  Below-gap no-single-particle-leakage law.

  This is supplied because perfect/no-leakage behavior depends on the concrete
  interface model.
  -/
  no_leakage_below_gap :
    ∀ ε : ℝ, ε < gapDelta → leakage ε = 0

namespace PoincareAndreevBoundary

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (S : PoincareAndreevBoundary V)

/-- Below the installed gap, leakage vanishes by supplied law. -/
theorem leakage_eq_zero_below_gap
    (ε : ℝ)
    (hε : ε < S.gapDelta) :
    S.leakage ε = 0 :=
  S.no_leakage_below_gap ε hε

end PoincareAndreevBoundary

end InfoGeometry.OperatorAlgebra.PoincareAndreev

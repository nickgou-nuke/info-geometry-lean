/-
InfoGeometry/OperatorAlgebra/PoincareAndreev.lean

Poincare-Andreev boundary socket.

Below-gap no-leakage and perfect-reflection behavior are supplied as interface
laws. This module does not infer perfect Andreev reflection from `epsilon < Δ`
alone.
-/

import Mathlib
import InfoGeometry.OperatorAlgebra.AndreevBoundary

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PoincareAndreev

open InfoGeometry.OperatorAlgebra.AndreevBoundary

/--
Poincare-Andreev boundary socket.

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
  no_leakage_below_gap_law :
    ∀ ε : ℝ, ε < gapDelta → leakage ε = 0

  /--
  Optional perfect-Andreev-efficiency law.

  This is stronger than no single-particle leakage and requires extra interface
  assumptions.
  -/
  perfect_reflection_below_gap_law :
    Prop

  /-- Proof/certificate of the perfect-reflection law. -/
  perfect_reflection_below_gap_certificate :
    perfect_reflection_below_gap_law

namespace PoincareAndreevBoundary

variable
    {V : Type*} [AddCommGroup V] [Module ℝ V]

variable (S : PoincareAndreevBoundary V)

/-- Below the installed gap, leakage vanishes by supplied law. -/
theorem leakage_eq_zero_below_gap
    (ε : ℝ)
    (hε : ε < S.gapDelta) :
    S.leakage ε = 0 :=
  S.no_leakage_below_gap_law ε hε

/-- The perfect-reflection certificate is available when installed. -/
theorem perfect_reflection_valid :
    S.perfect_reflection_below_gap_law :=
  S.perfect_reflection_below_gap_certificate

end PoincareAndreevBoundary

end InfoGeometry.OperatorAlgebra.PoincareAndreev

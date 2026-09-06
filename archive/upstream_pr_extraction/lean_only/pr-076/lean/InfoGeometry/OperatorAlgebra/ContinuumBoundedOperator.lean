import InfoGeometry.Krein.DoubledSpace
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Continuum Bounded Operator Layer (L1)

This module establishes the native continuum bounded operator layer for InfoGeometry.
Following the strict derivation chain, we start directly from the deepest root (L0):
the real `DoubledSpace E` carrier.

Bounded operators are strictly rooted as continuous linear maps over the real doubled
Hilbert space (`DoubledSpace E →L[ℝ] DoubledSpace E`), inheriting the submultiplicative
operator norm structure from Mathlib without hanging abstractions.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.Continuum

open InfoGeometry.Krein

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
L1 Root: The native space of Continuum Bounded Operators over the doubled state space.
Instead of an abstract `E →L[ℂ] F`, we root directly into the finite real doubled
carrier: `DoubledSpace E →L[ℝ] DoubledSpace E`.
-/
abbrev ContinuumBoundedOperator := DoubledSpace E →L[ℝ] DoubledSpace E

/--
Composition of two continuum bounded operators.
-/
abbrev compOperator (A B : ContinuumBoundedOperator E) : ContinuumBoundedOperator E :=
  A.comp B

/--
Submultiplicativity of the operator norm in the continuum on the doubled root.
This roots the fundamental `‖A B‖ ≤ ‖A‖ ‖B‖` inequality strictly onto the
`DoubledSpace` operator algebra.
-/
theorem norm_compOperator_le (A B : ContinuumBoundedOperator E) :
    ‖compOperator E A B‖ ≤ ‖A‖ * ‖B‖ :=
  ContinuousLinearMap.opNorm_comp_le A B

/-! ### Dual Operators on the Doubled Carrier -/

/--
The Riesz representation functional for the doubled space.
Maps a state vector in `DoubledSpace E` to its bounded dual functional.
-/
def stateDualOperator [CompleteSpace E] (v : DoubledSpace E) : DoubledSpace E →L[ℝ] ℝ :=
  innerSL ℝ v

end InfoGeometry.OperatorAlgebra.Continuum

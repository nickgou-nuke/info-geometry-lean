import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.ConformalLift55
import InfoGeometry.Canonical.Cl55V4SpinorFragmentation

/-!
# Klein Boundary States

This module packages the concrete `Cl(5,5)` spinor decomposition used by the
`Cl55V4SpinorFragmentation` bridge into the language of boundary sectors.

- `spinorPlus p = u + v` is the `J`-fixed sector.
- `spinorMinus p = u - v` is the `J`-anti-fixed sector.
- `S` (projective involution) acts analogously.
-/

noncomputable section

namespace InfoGeometry.Canonical.KleinBoundaryStates

open InfoGeometry.Clifford.ConformalLift55
open InfoGeometry.Canonical.Cl55V4SpinorFragmentation

/-- Plus-sector boundary state in the spinor module. -/
def boundaryPlus (p : ConformalNullPair) : Cl55 := spinorPlus p

/-- Minus-sector boundary state in the spinor module. -/
def boundaryMinus (p : ConformalNullPair) : Cl55 := spinorMinus p

/-- The `+` sector is fixed by Clifford inversion sandwich. -/
theorem boundary_plus_J_fixed (p : ConformalNullPair) :
    J p * boundaryPlus p * J p = boundaryPlus p :=
  spinorPlus_fixed_by_J p

/-- The `-` sector is anti-fixed by Clifford inversion sandwich. -/
theorem boundary_minus_J_anti (p : ConformalNullPair) :
    J p * boundaryMinus p * J p = -boundaryMinus p :=
  spinorMinus_anti_by_J p

/-- The same boundary split is seen by the projective involution. -/
theorem boundary_plus_S_fixed (p : ConformalNullPair) :
    S p * boundaryPlus p * S p = boundaryPlus p :=
  spinorPlus_fixed_by_S p

/-- The same boundary split is seen by the projective involution. -/
theorem boundary_minus_S_anti (p : ConformalNullPair) :
    S p * boundaryMinus p * S p = -boundaryMinus p :=
  spinorMinus_anti_by_S p

/-- `J` and `S` both act as involutions by conjugation on spinor operators. -/
theorem boundary_sandwich_involutions (p : ConformalNullPair) (x : Cl55) :
    J p * (J p * x * J p) * J p = x ∧
    S p * (S p * x * S p) * S p = x := by
  constructor
  · exact J_sandwich_involution p x
  · exact S_sandwich_involution p x

end InfoGeometry.Canonical.KleinBoundaryStates

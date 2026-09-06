import InfoGeometry.Physics.MatrixTraceBimodulePairingNative

namespace InfoGeometry.Physics

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The commutator direction in the matrix trace bimodule. -/
def commutatorDriver (A X : TraceOperatorSpace n) : TraceOperatorSpace n :=
  commutatorActionNative A X

/-- The Jordan direction in the matrix trace bimodule.

This is only a trace-pairing-symmetric algebraic direction.  No positivity,
normalization, or thermodynamic interpretation is asserted here.
-/
def jordanDriver (A X : TraceOperatorSpace n) : TraceOperatorSpace n :=
  jordanActionNative A X

/-- The algebraic sum of the commutator and Jordan directions. -/
def traceJordanLieDriverSum (A B X : TraceOperatorSpace n) : TraceOperatorSpace n :=
  commutatorDriver A X + jordanDriver B X

theorem commutatorDriver_tracePairing_skew (A X Y : TraceOperatorSpace n) :
    tracePairingNative (commutatorDriver A X) Y =
      -tracePairingNative X (commutatorDriver A Y) := by
  exact commutator_tracePairing_native A X Y

theorem jordanDriver_tracePairing_symmetric (A X Y : TraceOperatorSpace n) :
    tracePairingNative (jordanDriver A X) Y =
      tracePairingNative X (jordanDriver A Y) := by
  exact jordan_tracePairing_native A X Y

theorem commutatorDriver_energy_orthogonal (A X : TraceOperatorSpace n) :
    tracePairingNative A (commutatorDriver A X) = 0 := by
  exact commutator_tracePairing_energyOrthogonal A X

end InfoGeometry.Physics

import InfoGeometry.Physics.TraceJordanLieDriverBridge

namespace InfoGeometry.Physics

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conservative, Hamiltonian-style driver in the trace bimodule. -/
def conservativeDriver (H X : TraceOperatorSpace n) : TraceOperatorSpace n :=
  commutatorDriver H X

/-- Dissipative, Jordan-style driver in the trace bimodule. -/
def dissipativeDriver (S X : TraceOperatorSpace n) : TraceOperatorSpace n :=
  jordanDriver S X

/-- Combined algebraic driver. This is the trace-bimodule sum, not yet a
full density-matrix metriplectic flow law. -/
def metriplecticGenerator (H S X : TraceOperatorSpace n) : TraceOperatorSpace n :=
  conservativeDriver H X + dissipativeDriver S X

theorem conservative_driver_trace_skew (H X Y : TraceOperatorSpace n) :
    tracePairingNative (conservativeDriver H X) Y =
      - tracePairingNative X (conservativeDriver H Y) := by
  simpa [conservativeDriver] using
    commutatorDriver_tracePairing_skew (n := n) H X Y

theorem dissipative_driver_trace_symmetric (S X Y : TraceOperatorSpace n) :
    tracePairingNative (dissipativeDriver S X) Y =
      tracePairingNative X (dissipativeDriver S Y) := by
  simpa [dissipativeDriver] using
    jordanDriver_tracePairing_symmetric (n := n) S X Y

theorem conservative_energy_conservation (H X : TraceOperatorSpace n) :
    tracePairingNative H (conservativeDriver H X) = 0 := by
  simpa [conservativeDriver] using
    commutatorDriver_energy_orthogonal (n := n) H X

end InfoGeometry.Physics

import InfoGeometry.Physics.MatrixTraceBimodulePairingNative

/-!
# Ad-skewness of the finite trace pairing

This owner isolates the algebraic Killing identity from any exponential-flow
or analytic functional-calculus claims.
-/

namespace InfoGeometry.Physics.ModularTracePairingAdSkew

open InfoGeometry.Physics

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem tracePairing_ad_skew
    (K X Y : TraceOperatorSpace n) :
    tracePairingNative (commutatorActionNative K X) Y +
        tracePairingNative X (commutatorActionNative K Y) = 0 := by
  rw [commutator_tracePairing_native]
  abel

theorem tracePairing_generator_derivation_zero
    (K X : TraceOperatorSpace n) :
    tracePairingNative K (commutatorActionNative K X) = 0 := by
  exact commutator_tracePairing_energyOrthogonal K X

theorem tracePairing_ad_skew_eq_neg
    (K X Y : TraceOperatorSpace n) :
    tracePairingNative (commutatorActionNative K X) Y =
      -tracePairingNative X (commutatorActionNative K Y) := by
  exact commutator_tracePairing_native K X Y

end InfoGeometry.Physics.ModularTracePairingAdSkew

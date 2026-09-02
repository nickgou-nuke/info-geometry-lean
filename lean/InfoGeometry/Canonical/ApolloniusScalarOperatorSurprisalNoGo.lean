import InfoGeometry.Canonical.ApolloniusSurprisalCriticalLineBridge
import InfoGeometry.OperatorAlgebra.CanonicalZornSurprisalCurrent

/-!
# Central scalar surprisal lift: a no-go theorem

The scalar Apollonius negative-log potential can be embedded in the canonical
operator algebra as a scalar multiple of the identity.  That embedding is
central, so its derivation/commutator current vanishes identically.

Consequently, a nonzero operator surprisal current requires a genuinely
noncentral operator-valued lift.  Coordinate quantization or scalar
multiplication by the identity alone does not establish flux quantization.
-/

noncomputable section

namespace InfoGeometry.Canonical.ApolloniusScalarOperatorSurprisalNoGo

open InfoGeometry.Canonical.NegativeLogReadoutBridge
open InfoGeometry.OperatorAlgebra.CanonicalZornSurprisalCurrent

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ
abbrev ZornDer :=
  InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations

/-- Central embedding of a real scalar into the canonical endomorphism
algebra. -/
def scalarOperator (c : ℝ) : EndCZ :=
  c • (1 : EndCZ)

@[simp] theorem scalarOperator_apply (c : ℝ) (x : CZ) :
    scalarOperator c x = c • x := by
  simp [scalarOperator]

/-- Every scalar identity operator commutes with every canonical Zorn
derivation. -/
theorem scalarOperator_commutes
    (c : ℝ) (D : ZornDer) :
    D.1 * scalarOperator c = scalarOperator c * D.1 := by
  apply LinearMap.ext
  intro x
  simp [scalarOperator, Module.End.mul_apply]

/-- The Chevalley--Eilenberg surprisal current of a scalar identity lift is
identically zero. -/
theorem scalarOperator_surprisalCurrent_eq_zero
    (c : ℝ) :
    surprisalCurrent (scalarOperator c) = 0 := by
  apply LinearMap.ext
  intro D
  simpa using
    surprisalCurrent_eq_zero_of_commutes
      (scalarOperator c) D (scalarOperator_commutes c D)

/-- Central operator lift of the scalar Apollonius negative-log readout. -/
def apolloniusScalarSurprisalOperator (ξ θ : ℝ) : EndCZ :=
  scalarOperator (apolloniusRadialNegativeLog ξ θ)

/-- The centrally lifted Apollonius scalar potential has zero operator
surprisal current for every scale and phase. -/
theorem apolloniusScalarSurprisalCurrent_eq_zero
    (ξ θ : ℝ) :
    surprisalCurrent (apolloniusScalarSurprisalOperator ξ θ) = 0 := by
  exact scalarOperator_surprisalCurrent_eq_zero
    (apolloniusRadialNegativeLog ξ θ)

/-- On the zero-scale leaf, the central Apollonius operator itself is zero. -/
@[simp] theorem apolloniusScalarSurprisalOperator_zero_scale
    (θ : ℝ) :
    apolloniusScalarSurprisalOperator 0 θ = 0 := by
  simp [apolloniusScalarSurprisalOperator, scalarOperator]

end InfoGeometry.Canonical.ApolloniusScalarOperatorSurprisalNoGo

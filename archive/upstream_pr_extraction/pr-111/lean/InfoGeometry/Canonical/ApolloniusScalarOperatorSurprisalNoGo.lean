import Mathlib.LinearAlgebra.Trace
import InfoGeometry.Canonical.ApolloniusSurprisalCriticalLineBridge
import InfoGeometry.OperatorAlgebra.CanonicalZornSurprisalCurrent
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

/-!
# Central scalar surprisal lift: no-go theorems

The scalar Apollonius negative-log potential can be embedded in the canonical
operator algebra as a scalar multiple of the identity.  That embedding is
central, so its derivation/commutator current vanishes identically.

Moreover, the native circular Zorn carrier is finite-dimensional.  Hence no
pair of its endomorphisms has a commutator equal to a nonzero scalar multiple
of the identity: the commutator has trace zero, while the proposed right-hand
side has trace `8c`.

Consequently, a nonzero operator surprisal current requires a genuinely
noncentral operator-valued lift, and an exact canonical commutation relation
requires an infinite-dimensional or otherwise non-finite trace setting.
Coordinate quantization alone does not establish flux quantization.
-/

noncomputable section

namespace InfoGeometry.Canonical.ApolloniusScalarOperatorSurprisalNoGo

open InfoGeometry.Canonical.NegativeLogReadoutBridge
open InfoGeometry.OperatorAlgebra.CanonicalZornSurprisalCurrent
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

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

/-- The canonical real Zorn carrier has dimension eight, read directly from
its circular Peirce basis. -/
theorem canonicalZorn_finrank_eight :
    Module.finrank ℝ CZ = 8 := by
  rw [Module.finrank_eq_card_basis circularPeirceBasis]
  exact Fintype.card_fin 8

/-- No finite-dimensional canonical Zorn operators satisfy an exact
commutator relation with a nonzero scalar identity on the right. -/
theorem no_exact_nonzero_scalar_commutator
    (A B : EndCZ) (c : ℝ) (hc : c ≠ 0) :
    A * B - B * A ≠ scalarOperator c := by
  letI : Module.Free ℝ CZ := Module.Free.of_basis circularPeirceBasis
  letI : Module.Finite ℝ CZ := Module.Finite.of_basis circularPeirceBasis
  intro h
  have hcomm :
      LinearMap.trace ℝ CZ (A * B - B * A) = 0 := by
    simpa [Ring.lie_def] using
      (LinearMap.trace_lie A B)
  have hscalar :
      LinearMap.trace ℝ CZ (scalarOperator c) = c * 8 := by
    simp [scalarOperator, canonicalZorn_finrank_eight]
  have htrace := congrArg (LinearMap.trace ℝ CZ) h
  rw [hcomm, hscalar] at htrace
  apply hc
  linarith

/-- In particular, an exact real canonical commutation relation
`[A,B] = c I` forces `c = 0` on the native eight-dimensional carrier. -/
theorem scalar_commutator_coefficient_eq_zero
    (A B : EndCZ) (c : ℝ)
    (h : A * B - B * A = scalarOperator c) :
    c = 0 := by
  by_contra hc
  exact no_exact_nonzero_scalar_commutator A B c hc h

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

import InfoGeometry.Quantum.GeometricTensorMixedPullback
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CanonicalZornSpinVectorAction

/-!
# Typed canonical Zorn triality for a spin-flow/QGT bridge

This file deliberately stops at the repository's current boundary.  It
consumes a supplied spin-group flow and reuses the proved vector/half-spin
covariance theorem; it does not assert that an arbitrary split-octonion
derivation has already been lifted to such a flow.
-/

noncomputable section

namespace InfoGeometry.Quantum.ChiralSpinDerivationQGTBridge

open InfoGeometry.Physics.SplitOctonionBraidSU3
open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open CanonicalZornSpinChirality
open CanonicalZornSpinRelatedFiber
open CanonicalZornOuterTrialityGroup
open InfoGeometry.Canonical.CanonicalZornSpinVectorAction

/-- A supplied flow in the canonical typed Zorn spin carrier. -/
def vectorFlow (g : ℝ → ComplexSpin44) (t : ℝ) : Module.End ℂ Vector8 :=
  spinVectorLinear (g t)

def plusFlow (g : ℝ → ComplexSpin44) (t : ℝ) : SpinorPlus8 → SpinorPlus8 :=
  spinorPlusAct (complexSpinPlusRepresentation (g t))

def minusFlow (g : ℝ → ComplexSpin44) (t : ℝ) : SpinorMinus8 → SpinorMinus8 :=
  spinorMinusAct (complexSpinMinusRepresentation (g t))

theorem plus_clifford_covariance
    (g : ℝ → ComplexSpin44) (t : ℝ) (V : Vector8) (S : SpinorPlus8) :
    minusFlow g t (cliffordPlus V S) =
      cliffordPlus (vectorFlow g t V) (plusFlow g t S) := by
  exact complexSpin_cliffordPlus_equivariant (g t) V S

theorem minus_clifford_covariance
    (g : ℝ → ComplexSpin44) (t : ℝ) (V : Vector8) (C : SpinorMinus8) :
    plusFlow g t (cliffordMinus V C) =
      cliffordMinus (vectorFlow g t V) (minusFlow g t C) := by
  exact complexSpin_cliffordMinus_equivariant (g t) V C

theorem triality_covariance
    (g : ℝ → ComplexSpin44) (t : ℝ) (V : Vector8)
    (S : SpinorPlus8) (C : SpinorMinus8) :
    vectorQuadratic (vectorFlow g t V) = vectorQuadratic V ∧
    minusFlow g t (cliffordPlus V S) =
      cliffordPlus (vectorFlow g t V) (plusFlow g t S) ∧
    plusFlow g t (cliffordMinus V C) =
      cliffordMinus (vectorFlow g t V) (minusFlow g t C) := by
  exact complexSpin_vector_halfSpin_triality_bridge (g t) V S C

end InfoGeometry.Quantum.ChiralSpinDerivationQGTBridge

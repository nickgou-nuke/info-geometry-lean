import InfoGeometry.Physics.FourVectorDiracReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.ChiralFourVectorOperatorSynthesis
import InfoGeometry.Canonical.ChiralPatternParallelBridge

/-!
# Four-vector invariant synthesis

This is a consolidation owner for the finite four-vector interfaces already
proved in the repository.  It deliberately keeps momentum, Jones/Stokes, and
operator-valued chiral carriers distinct; the theorem packet records their
common invariant readouts without asserting an intertwiner between carriers.
-/

noncomputable section

namespace InfoGeometry.Physics.FourVectorInvariantSynthesis

open InfoGeometry.Physics.ChiralPoincareSouriauBridge
open InfoGeometry.Physics.LorentzBoostMinkowski
open InfoGeometry.Clifford.DiracPauliGamma
open InfoGeometry.Physics.FourVectorDiracReadout
open InfoGeometry.Physics.ChiralFourVectorOperatorSynthesis
open InfoGeometry.Physics.LorentzChiralCuntzBridge
open InfoGeometry.Optics.JonesPoincareSphere

/-! The finite invariant packet: Dirac square, Lorentz covariance, and null
Stokes readout. -/
theorem finite_four_vector_invariant_packet
    (pD : InfoGeometry.Physics.LorentzBoostMinkowski.FourVector)
    (pM : FourMomentum) (g : SL2C) (J : JonesSpinor) :
    diracSlash pD * diracSlash pD =
        (InfoGeometry.Physics.LorentzBoostMinkowski.minkowskiSq pD : ℂ) •
          (1 : DiracMatrix) ∧
      pauliMomentum (spinLorentzAction g pM) =
        chiralConjAct g (pauliMomentum pM) ∧
      minkowskiSq (spinLorentzAction g pM) = minkowskiSq pM ∧
      (JonesSpinor.stokesMinkowski4 J).q = 0 := by
  exact ⟨diracSlash_sq pD,
    (by rw [spinLorentzAction, pauliMomentum_fourMomentumOfMatrix]),
    spinLorentzAction_preserves_minkowskiSq g pM,
    JonesSpinor.stokesMinkowski4_q J⟩

/-! The operator-valued chiral carrier exposes the same two algebraic
projections: mixed products give the diagonal/dot channel, while the
same-sheet product gives the oriented cross channel. -/
theorem chiral_operator_four_vector_channels
    {A : Type*} [Ring A]
    (U V : InfoGeometry.Canonical.OperatorVector A) :
    InfoGeometry.Canonical.operatorZornMul
          (InfoGeometry.Canonical.sigmaPlus U)
          (InfoGeometry.Canonical.sigmaMinus V) =
        InfoGeometry.Canonical.nPlus
          (InfoGeometry.Canonical.operatorDot U V) ∧
      InfoGeometry.Canonical.operatorZornMul
          (InfoGeometry.Canonical.sigmaMinus V)
          (InfoGeometry.Canonical.sigmaPlus U) =
        InfoGeometry.Canonical.nMinus
          (InfoGeometry.Canonical.operatorDot V U) ∧
      InfoGeometry.Canonical.operatorZornMul
          (InfoGeometry.Canonical.sigmaPlus U)
          (InfoGeometry.Canonical.sigmaPlus V) =
        InfoGeometry.Canonical.sigmaMinus
          (InfoGeometry.Canonical.operatorCross U V) := by
  exact InfoGeometry.Canonical.ChiralPatternParallelBridge.split_operator_four_vector_product_channels U V

end InfoGeometry.Physics.FourVectorInvariantSynthesis

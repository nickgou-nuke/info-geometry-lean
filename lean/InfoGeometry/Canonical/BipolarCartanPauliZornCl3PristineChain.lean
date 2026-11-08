import InfoGeometry.Canonical.BipolarCartanCl3PhaseBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Pristine Cartan--Pauli--Zorn--`Cl(3)` chain

This capstone states the exact finite reconstruction supported by the current
repository:

* the boost and circular generators are independent over `ℝ` and dependent
  over `ℂ` inside one trace-zero Cartan line;
* conjugation by the half-log lift realizes the four Pauli light-cone and
  circular weights;
* the acted Pauli determinant equals the Minkowski quadratic form, the
  corrected real Zorn norm, and the circular Witt diagonal form;
* the injective realification preserves the Cartan split, inverse identities,
  and the double-sided Pauli action;
* after the explicit coordinate-order permutation, multiplication by `I` is
  the concrete real Pauli `Cl(3)` volume axis.

The theorem deliberately stops before the unproved identifications with a
concrete graded `Cl(1,3)` spacetime algebra, a split-octonion algebra
homomorphism, `G₂(2)` derivations, or a Nambu--Krein spinor functor.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarCartanPauliZornCl3PristineChain

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Canonical.BipolarLogSL2
open InfoGeometry.Canonical.BipolarCartanLorentzBridge
open InfoGeometry.Canonical.BipolarComplexCartanLine
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.BipolarPauliHestenesSolderingBridge
open InfoGeometry.Canonical.BipolarPauliZornWittBridge
open InfoGeometry.Canonical.BipolarCartanPauliZornRealificationBridge
open InfoGeometry.Canonical.BipolarCartanCl3PhaseBridge
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.Canonical.Cl11JordanComplexRealificationBridge
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Lie.SplitOctonionCircularWittForm
open InfoGeometry.Clifford.GullDoranPseudoscalarBridge

abbrev Matrix4R := InfoGeometry.Algebra.FiniteSpin.Mat4R

/-- Complete finite theorem packet for the reconstructed representation chain. -/
theorem bipolar_cartan_pauli_zorn_cl3_pristine_chain
    (s : ℂ) (P : PauliParavector) :
    Kcirc = Complex.I • Kboost ∧
      (∀ a b : ℝ,
        (a : ℂ) • Kboost + (b : ℂ) • Kcirc = 0 →
          a = 0 ∧ b = 0) ∧
      bipolarLogarithmicCartan s ∈ cartanLine ∧
      Matrix.trace (bipolarLogarithmicCartan s) = 0 ∧
      (bipolarSolderingAction s (pauliHermitian P)).mat =
        matrixOfCartanCoordinates
          (bipolarCoordinateAction s (pauliCartanCoordinates P)) ∧
        zornNorm (pauliZorn P) = P.minkowskiNormSq ∧
      circularWittQuadratic
          (minkowskiDiagonalEmbedding (pauliMomentumCoordinates P)) =
        P.minkowskiNormSq ∧
      Matrix.det (bipolarSolderingAction s (pauliHermitian P)).mat =
        ((zornNorm (pauliZorn P) : ℝ) : ℂ) ∧
      realifiedKcirc = complexStructure * realifiedKboost ∧
      complexStructure * complexStructure = -(1 : Matrix4R) ∧
      realifiedLogarithmicCartanGenerator s =
        eta s • realifiedKboost +
          theta s • (complexStructure * realifiedKboost) ∧
      realifiedHalfLogLift s * realifiedHalfLogLiftInv s = 1 ∧
      realifiedBipolarPauliAction s P =
        realifiedHalfLogLift s * realifiedPauliMatrix P *
          realify (Matrix.conjTranspose (halfLogLift s)) ∧
      realificationOrderSwap * complexStructure * realificationOrderSwap =
        realSigma1 * realSigma2 * realSigma3 ∧
      (realSigma1 * realSigma2 * realSigma3) *
          (realSigma1 * realSigma2 * realSigma3) =
        -(1 : Matrix4R) ∧
      interleavedKcirc =
        (realSigma1 * realSigma2 * realSigma3) * interleavedKboost := by
  exact ⟨cartan_real_complex_rank_packet.1,
    cartan_real_complex_rank_packet.2,
    bipolarLogarithmicCartan_mem_cartanLine s,
    bipolarLogarithmicCartan_trace_zero s,
    bipolarSolderingAction_pauliMatrix s P,
    zornNorm_pauliZorn P,
    circularWittQuadratic_pauli P,
    bipolarSolderingAction_det_eq_zornNorm s P,
    realifiedKcirc_eq_complexStructure_mul_realifiedKboost,
    complexStructure_sq,
    realifiedLogarithmicCartanGenerator_complexStructure_split s,
    realifiedHalfLogLift_mul_inv s,
    realifiedBipolarPauliAction_factorization s P,
    orderSwap_complexStructure_eq_real_pauli_volume,
    real_pauli_volume_sq,
    interleavedKcirc_eq_real_pauli_volume_mul_interleavedKboost⟩

end InfoGeometry.Canonical.BipolarCartanPauliZornCl3PristineChain

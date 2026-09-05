import InfoGeometry.Canonical.BipolarComplexCartanLine
import InfoGeometry.Canonical.BipolarPauliHestenesSolderingBridge
import InfoGeometry.Canonical.BipolarPauliZornWittBridge

/-!
# Pristine Pauli--Zorn realization of the bipolar Cartan action

This capstone contains no new interpretation. It combines the proved finite
bridges:

* the two real Cartan directions form one trace-zero complex Cartan line;
* the abstract four Cartan weights are the actual entries of the conjugated
  Pauli/Hestenes matrix;
* the preserved Pauli determinant equals both the corrected Zorn norm and the
  circular Witt diagonal quadratic form.

No algebra equivalence between `M₂(ℂ)` and the split-octonion carrier is
claimed.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarPauliZornPristineChain

open InfoGeometry.Canonical.BipolarComplexCartanLine
open InfoGeometry.Canonical.BipolarPauliHestenesSolderingBridge
open InfoGeometry.Canonical.BipolarPauliZornWittBridge
open InfoGeometry.Canonical.BipolarCartanLorentzBridge
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.PauliHestenesSpinMomentum
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Lie.SplitOctonionCircularWittForm

abbrev PauliVector :=
  InfoGeometry.Canonical.PauliHestenesSpinMomentum.PauliParavector

/-- Complete finite realization packet for one paravector. -/
theorem bipolar_pauli_zorn_pristine_chain
    (s : ℂ) (P : PauliVector) :
    Kcirc = Complex.I • Kboost ∧
      (∀ a b : ℝ,
        (a : ℂ) • Kboost + (b : ℂ) • Kcirc = 0 →
          a = 0 ∧ b = 0) ∧
      logarithmicCartanGenerator s ∈ cartanLine ∧
      Matrix.trace (logarithmicCartanGenerator s) = 0 ∧
      (bipolarSolderingAction s (pauliHermitian P)).mat =
        matrixOfCartanCoordinates
          (bipolarCoordinateAction s (pauliCartanCoordinates P)) ∧
      ZornMatrix.zornNorm (pauliZorn P) = P.minkowskiNormSq ∧
      circularWittQuadratic
          (minkowskiDiagonalEmbedding (pauliMomentumCoordinates P)) =
        P.minkowskiNormSq ∧
      Matrix.det (bipolarSolderingAction s (pauliHermitian P)).mat =
        (ZornMatrix.zornNorm (pauliZorn P) : ℂ) := by
  exact ⟨cartan_real_complex_rank_packet.1,
    cartan_real_complex_rank_packet.2,
    logarithmicCartanGenerator_mem_cartanLine s,
    logarithmicCartanGenerator_trace_zero s,
    bipolarSolderingAction_pauliMatrix s P,
    zornNorm_pauliZorn P,
    circularWittQuadratic_pauli P,
    bipolarSolderingAction_det_eq_zornNorm s P⟩

end InfoGeometry.Canonical.BipolarPauliZornPristineChain

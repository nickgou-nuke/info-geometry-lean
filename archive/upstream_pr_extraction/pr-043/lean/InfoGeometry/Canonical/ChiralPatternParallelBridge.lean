import InfoGeometry.Canonical.PeirceChiralOperatorBridge
import InfoGeometry.Canonical.SplitOctonionThreeColorMatrixRepresentation
import InfoGeometry.Canonical.ThreeColorOperatorCrossCommutator
import InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge

/-!
# Parallel chiral Peirce patterns

This owner packages the carrier-independent consequences of the existing
Jones and associative matrix-unit owners.  It intentionally proves no
equivalence between those carriers and no representation theorem for the
non-associative Zorn carrier.
-/

namespace InfoGeometry.Canonical.ChiralPatternParallelBridge

open PeirceChiralOperatorPacket

variable {A : Type*} [Ring A] (P : PeirceChiralOperatorPacket A)

theorem odd_odd_sum_eq_identity :
    P.sigmaPlus * P.sigmaMinus + P.sigmaMinus * P.sigmaPlus = 1 := by
  rw [P.sigmaPlus_mul_sigmaMinus, P.sigmaMinus_mul_sigmaPlus]
  exact P.p_sum

theorem odd_odd_difference_eq_parity :
    P.sigmaPlus * P.sigmaMinus - P.sigmaMinus * P.sigmaPlus = P.parity := by
  rw [P.sigmaPlus_mul_sigmaMinus, P.sigmaMinus_mul_sigmaPlus]
  rfl

theorem parity_is_involution : P.parity * P.parity = 1 :=
  P.parity_sq

theorem odd_square_zero :
    P.sigmaPlus * P.sigmaPlus = 0 ∧ P.sigmaMinus * P.sigmaMinus = 0 :=
  ⟨P.sigmaPlus_sq, P.sigmaMinus_sq⟩

theorem superconnection_channels :
    (P.sigmaPlus * P.sigmaMinus + P.sigmaMinus * P.sigmaPlus = 1) ∧
      (P.sigmaPlus * P.sigmaMinus - P.sigmaMinus * P.sigmaPlus = P.parity) :=
  ⟨odd_odd_sum_eq_identity P, odd_odd_difference_eq_parity P⟩

/-! The two concrete owners expose exactly the same defining equations. -/

theorem jones_odd_odd_channels :
    InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge.sigmaPlus *
          InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge.sigmaMinus +
        InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge.sigmaMinus *
          InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge.sigmaPlus = 1 ∧
      InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge.circularCommutator
          InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge.sigmaPlus
          InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge.sigmaMinus =
        InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge.circularPlus -
          InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge.circularMinus :=
  ⟨InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge.sigmaPlus_oddOdd_eq_identity,
    InfoGeometry.Optics.CircularPolarizationSuperconnectionBridge.sigmaPlus_ordinary_commutator_eq_helicity⟩

theorem split_matrix_odd_odd_channels :
    InfoGeometry.Canonical.SplitOctonionThreeColorMatrixRepresentation.sigmaPlus *
          InfoGeometry.Canonical.SplitOctonionThreeColorMatrixRepresentation.sigmaMinus +
        InfoGeometry.Canonical.SplitOctonionThreeColorMatrixRepresentation.sigmaMinus *
          InfoGeometry.Canonical.SplitOctonionThreeColorMatrixRepresentation.sigmaPlus =
        (1 : InfoGeometry.Canonical.SplitOctonionThreeColorMatrixRepresentation.M₂) := by
  rw [InfoGeometry.Canonical.SplitOctonionThreeColorMatrixRepresentation.sigmaPlus_mul_sigmaMinus,
    InfoGeometry.Canonical.SplitOctonionThreeColorMatrixRepresentation.sigmaMinus_mul_sigmaPlus,
    ← InfoGeometry.Canonical.SplitOctonionThreeColorMatrixRepresentation.nPlus_add_nMinus]

theorem split_operator_four_vector_product_channels
    {A : Type*} [Ring A] (U V : OperatorVector A) :
    operatorZornMul (sigmaPlus U) (sigmaMinus V) = nPlus (operatorDot U V) ∧
      operatorZornMul (sigmaMinus V) (sigmaPlus U) = nMinus (operatorDot V U) ∧
      operatorZornMul (sigmaPlus U) (sigmaPlus V) = sigmaMinus (operatorCross U V) :=
  ⟨sigmaPlus_mul_sigmaMinus U V, sigmaMinus_mul_sigmaPlus V U,
    sigmaPlus_mul_sigmaPlus U V⟩

end InfoGeometry.Canonical.ChiralPatternParallelBridge

import InfoGeometry.Clifford.ParaKahler55PositiveGrassmannianCantorBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStarRepresentationBridge
import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge

/-!
# Cl(5,5) spinor matrices represented on the Cantor Bernoulli boundary

The finite Cantor matrix-stage owner already represents `BitWordMatrixStage n`
on the actual Bernoulli-boundary `L²` space.  This module transports the
existing real 32-dimensional spinor matrix representation through that stage
at depth five.  The coefficient extension `ℝ → ℂ` and the finite index
reindexing are explicit; the endpoint is a bounded operator on `L2Boundary`.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55CantorL2SpinorBridge

open InfoGeometry.Clifford.ParaKahler55PositiveGrassmannianCantorBridge
open InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure
open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.MatrixPluckerPositiveBridge
open InfoGeometry.Projective.ExteriorPowerPluckerBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStageTransportBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixStarRepresentationBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport

abbrev SpinorMatrix := InfoGeometry.Clifford.SpinorRep.SpinorMatrix 5
abbrev L2Operator := BoundedL2Operator

/-- Extend coefficients of the real five-mode spinor matrices to `ℂ`, then
reindex them by the same length-five binary words used by the Cantor matrix
stage. -/
def spinorMatrixToBitWord : SpinorMatrix →+* BitWordMatrixStage 5 :=
  (bitWordStageStarAlgEquiv 5).symm.toRingEquiv.toRingHom.comp
    ((algebraMap ℝ ℂ).mapMatrix)

/-- The finite depth-five Cantor matrix representation on the boundary `L²`
space, with the real spinor coefficients extended to complex scalars. -/
def spinorMatrixL2Representation : SpinorMatrix →+* L2Operator :=
  (bitWordMatrixStarRepresentation 5).toRingHom.comp spinorMatrixToBitWord

/-- The existing `Cl(5,5)` spinor representation, now acting by bounded
operators on the Cantor Bernoulli `L²` space. -/
def cl55L2Representation : InfoGeometry.Clifford.Clifford55.Cl55 →+* L2Operator :=
  spinorMatrixL2Representation.comp
    InfoGeometry.Clifford.Clifford55.cl55SpinorAlgEquiv.toRingHom

/-- The exterior-spinor representation used by the positive Grassmannian
bridge, transported to actual bounded operators on Cantor `L²`. -/
def exterior55L2Representation : Exterior55 →+* L2Operator :=
  cl55L2Representation.comp twistorMapAlgHom.toRingHom

/-- The four-mode Grassmannian exterior algebra represented on the Cantor
boundary by its established inclusion into the five-mode exterior carrier. -/
def grassmannianL2Representation : ExteriorAlgebra ℝ Vec4 →+* L2Operator :=
  exterior55L2Representation.comp grassmannianExteriorRepresentation.toRingHom

/-- The positive Grassmannian quotient's normalized exterior blade has a
concrete bounded-operator readout on the Cantor Bernoulli boundary. -/
def positiveGrassmannianL2Readout (P : PositiveGrassmannian) : L2Operator :=
  exterior55L2Representation (positiveGrassmannianExteriorBlade P)

theorem grassmannianBlade_l2Readout (M : Matrix2x4) :
    grassmannianL2Representation (grassmannianExteriorBlade M) =
      exterior55L2Representation (positiveGrassmannianBlade M) := by
  rw [grassmannianL2Representation, RingHom.comp_apply]
  exact congrArg exterior55L2Representation
    (grassmannianExteriorRepresentation_blade M)

/-- For each strictly positive chart representative, its decomposable blade
is represented by the same two spinor-row generators as in the finite
spinor owner, now as an operator on `L²(Cantor)`. -/
theorem positiveGrassmannianChart_l2Readout
    (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    MatrixPluckerPositive M ∧
      grassmannianL2Representation (grassmannianExteriorBlade M) =
        exterior55L2Representation (positiveGrassmannianBlade M) := by
  exact ⟨positiveGrassmannianInterior_mem_matrixPluckerPositive M hM,
    grassmannianBlade_l2Readout M⟩

end InfoGeometry.Clifford.Cl55CantorL2SpinorBridge

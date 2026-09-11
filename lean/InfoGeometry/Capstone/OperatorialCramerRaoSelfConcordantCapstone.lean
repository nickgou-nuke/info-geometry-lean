import InfoGeometry.Canonical.OperatorialCramerRao
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearSelfConcordantBarrierBridge

/-!
# Operatorial Cramér--Rao and log-det curvature capstone

This file only joins two already-owned finite statements:

* the operatorial Cramér--Rao inverse bound on a comparison-state channel;
* the matrix-to-spectrum self-concordance inequality for a supplied spectral
  carrier.

The spectral carrier equality and the unit-response hypotheses remain explicit.
No identification with a nuclear Hamiltonian, BKM metric, or physical stability
claim is introduced here.
-/

namespace InfoGeometry.Capstone.OperatorialCramerRaoSelfConcordant

open InfoGeometry.Canonical.OperatorialCramerRao
open InfoGeometry.Canonical.OnsagerReciprocity
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Krein
open InfoGeometry.Analysis.SelfConcordant
open InfoGeometry.Analysis.MatrixSpectral
open InfoGeometry.Physics.NuclearBarrier

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {n : ℕ}

theorem operatorial_cramer_rao_and_matrix_barrier
    (comparison : DoubledSpace E)
    (X Y : PerturbationChannel E)
    (hUnit : comparisonStateGeneratorMetric comparison X Y = 1)
    (hY : Y comparison ≠ 0)
    (V : MatrixVariationConjugation n)
    (C : SymmetricSpectralCarrier n)
    (h_carrier : V.B = C.B) :
    1 / comparisonStateGeneratorMetric comparison Y Y
        ≤ comparisonStateGeneratorMetric comparison X X ∧
      |thirdDerivPhi V.A_inv V.H| ≤
        2 * (hessianQuad V.A_inv V.H) ^ (3 / 2 : ℝ) := by
  constructor
  · exact inv_comparisonStateGeneratorMetric_self_le_of_unit_response
      comparison X Y hUnit hY
  · exact matrix_self_concordance_barrier_bound V C h_carrier

end InfoGeometry.Capstone.OperatorialCramerRaoSelfConcordant

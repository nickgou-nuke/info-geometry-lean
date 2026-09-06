import proofs.BraidedCocycleWilsonEntropy
import proofs.VertexAlgebraBraidingCocycle
import proofs.EntropicChiralDeRhamDictionary
import proofs.EntropicChiralDeRhamFormalization
import proofs.ChiralConeAlgebraFinality
import proofs.ChiralPoincareSouriauBridge
import proofs.LightConeTripotentMatrixBridge
import proofs.SolderingSpinConnectionBogoliubov
import proofs.PrimonCuntzTower

/-!
# Chiral Wilson/de Rham/Dirac--Hodge graph identification

This file records finite graph, matrix, and stage-sequence identities connecting
Wilson logarithmic graph cochains, abstract de Rham `dlog` clocks, Pauli matrix
maps, chiral cone algebra relations, and the finite Cuntz Dirac--Hodge operator.
-/

noncomputable section

namespace ChiralWilsonDeRhamDiracHodgeGraphIdentification

open Matrix
open BraidedCocycleWilsonEntropy
open ChiralPoincareSouriauBridge
open InfoGeometry.Quantum.PrimonCuntzTower

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- The Pauli matrix map from the soldering module is definitionally equal to
the chiral Poincare momentum matrix. -/
theorem solder_eq_pauliMomentum (P : FourMomentum) :
    SolderingSpinConnectionBogoliubov.solder P.E P.px P.py P.pz =
      pauliMomentum P := by
  cases P with
  | mk E px py pz =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [SolderingSpinConnectionBogoliubov.solder,
          SolderingSpinConnectionBogoliubov.σ1,
          SolderingSpinConnectionBogoliubov.σ2,
          SolderingSpinConnectionBogoliubov.σ3,
          pauliMomentum, Matrix.smul_apply, Matrix.add_apply] <;> ring_nf

/-- The determinant of the soldering matrix is the corresponding quadratic
form of the four-momentum coordinates. -/
theorem solder_det_eq_minkowskiSq (P : FourMomentum) :
    (SolderingSpinConnectionBogoliubov.solder P.E P.px P.py P.pz).det =
      minkowskiSq P := by
  rw [solder_eq_pauliMomentum P]
  exact det_pauliMomentum P

/-- Finite conjunction of the Wilson/de Rham graph cochain identities, Pauli
matrix equalities, chiral cone algebra relations, and Cuntz Dirac--Hodge stage
sequence identities used in this file. -/
theorem chiral_wilson_deRham_diracHodge_graph_identification
    (n : ℕ) (f : Stage n) (P : FourMomentum) :
    triangleWilson entropyCycle = 3 ∧
    BrokenDetailedBalance entropyCycle ∧
    EntropicChiralDeRhamFormalization.triple_point_entropy_wilson_count =
      ⟨entropyCycle_wilson, entropyCycle_breaks_detailedBalance⟩ ∧
    SolderingSpinConnectionBogoliubov.solder P.E P.px P.py P.pz =
      pauliMomentum P ∧
    (SolderingSpinConnectionBogoliubov.solder P.E P.px P.py P.pz).det =
      minkowskiSq P ∧
    LightConeTripotentMatrixBridge.detQuadric (pauliMomentum P) =
      minkowskiSq P ∧
    (LightConeTripotentMatrixBridge.MatrixLightCone (pauliMomentum P) ↔
      minkowskiSq P = 0) ∧
    ChiralConeAlgebraFinality.sPlus * ChiralConeAlgebraFinality.sPlus = 0 ∧
    ChiralConeAlgebraFinality.sMinus * ChiralConeAlgebraFinality.sMinus = 0 ∧
    ChiralConeAlgebraFinality.NPlus + ChiralConeAlgebraFinality.NMinus =
      (1 : ChiralConeAlgebraFinality.M2C) ∧
    ChiralConeAlgebraFinality.s3 * ChiralConeAlgebraFinality.sPlus -
        ChiralConeAlgebraFinality.sPlus * ChiralConeAlgebraFinality.s3 =
      (2 : ℂ) • ChiralConeAlgebraFinality.sPlus ∧
    ChiralConeAlgebraFinality.s3 * ChiralConeAlgebraFinality.sMinus -
        ChiralConeAlgebraFinality.sMinus * ChiralConeAlgebraFinality.s3 =
      (-2 : ℂ) • ChiralConeAlgebraFinality.sMinus ∧
    diracHodgeCuntz n f = D_n n f ∧
    stageToSequence n (diracHodgeCuntz n f) =
      algebraicDirac (stageToSequence n f) ∧
    stageToSequence n (D_n n f) = algebraicDirac (stageToSequence n f) := by
  refine ⟨entropyCycle_wilson,
    entropyCycle_breaks_detailedBalance,
    ?_,
    solder_eq_pauliMomentum P,
    solder_det_eq_minkowskiSq P,
    LightConeTripotentMatrixBridge.detQuadric_pauliMomentum P,
    LightConeTripotentMatrixBridge.pauli_lightCone_iff_minkowski_null P,
    ChiralConeAlgebraFinality.sPlus_sq_zero,
    ChiralConeAlgebraFinality.sMinus_sq_zero,
    ChiralConeAlgebraFinality.chiral_projector_completeness,
    ?_, ?_, ?_,
    stageToSequence_diracHodgeCuntz n f,
    stageToSequence_D n f⟩
  · apply Subsingleton.elim
  · exact (ChiralConeAlgebraFinality.chiral_lie_axis_relations).1
  · exact (ChiralConeAlgebraFinality.chiral_lie_axis_relations).2
  · rw [diracHodgeCuntz_eq_D_n]

end ChiralWilsonDeRhamDiracHodgeGraphIdentification

end noncomputable section

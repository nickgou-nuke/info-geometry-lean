/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.CellularSheafOperatorPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import InfoGeometry.OperatorAlgebra.PeirceSpine.CayleyDicksonHopfPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorBogoliubovSpinePoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.KantorBogoliubovCrossGradeClosure
import InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeItFromBitLogisticPoset

/-!
# D₄₁: A precise operator Rosetta theorem

This module records exact polynomial identities among existing Peirce-spine
owners. “Geometry”, “physics”, and “information” are interpretation labels;
the theorem identifies operators on one associative ring carrier and does not
construct equivalences between geometric, physical, or information-theoretic
categories.

The dependency order is: Peirce split → tetraktys metric and commutator →
Bergman, sheaf, magnetic, and Hopf realizations → defect and Kantor identities.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

/-! ### Causal order -/

inductive RosettaStage where
  | peirceSplit
  | metricAndCurvature
  | unipotentProjectiveTransport
  | domainRealizations
  | defectAndKantorClosure
  deriving DecidableEq, Repr

def rosettaRank : RosettaStage → ℕ
  | .peirceSplit => 0
  | .metricAndCurvature => 1
  | .unipotentProjectiveTransport => 2
  | .domainRealizations => 3
  | .defectAndKantorClosure => 4

theorem rosettaRank_strict_chain :
    rosettaRank .peirceSplit < rosettaRank .metricAndCurvature ∧
    rosettaRank .metricAndCurvature < rosettaRank .unipotentProjectiveTransport ∧
    rosettaRank .unipotentProjectiveTransport < rosettaRank .domainRealizations ∧
    rosettaRank .domainRealizations < rosettaRank .defectAndKantorClosure := by
  decide

/-! ### Canonical finite operator identities -/

variable {B : Type*} [Ring B] [StarRing B]

omit [StarRing B] in
/-- The Bergman complement at the unit is the tetraktys metric. -/
theorem rosetta_bergman_metric {P : B} (hP : P * P = P) (A C : B) :
    1 - bergmanOp P A C 1 = genV P A C := by
  rcases archetype_A23_bergman_operator hP A C with ⟨h, _⟩
  rw [h]
  abel

omit [StarRing B] in
/-- The square of the grading-perturbed generator is `1 + V`. -/
theorem rosetta_bogoliubov_metric {P : B} (hP : P * P = P) (A C : B) :
    (invS P + genPhi P A C) * (invS P + genPhi P A C) = 1 + genV P A C :=
  grading_add_phi_sq hP A C

/-- The cellular sheaf Laplacian and magnetic adjacency square realize the same
metric, with the self-adjoint corner hypothesis made explicit. -/
theorem rosetta_sheaf_and_magnetic_metric
    {P : B} (hP : P * P = P) (hPs : star P = P) (A : B) :
    sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) = genV P A (star A) ∧
    magnetAdj P A * magnetAdj P A = genV P A (star A) := by
  refine ⟨(sheaf_to_tetraktys_bridge hP hPs A (star A)).2.2, ?_⟩
  exact (digrac_flow_imbalance_and_magnet_laplacian
    (P := P) hPs hP 0 A 0).2.2.2.2.2.2.2.2.2

/-- For arbitrary transition operators the sheaf quadratic operator is the
Gram product of the Peirce current. This does not require the cut to be
self-adjoint or identify the Gram product with `V`. -/
theorem rosetta_sheaf_laplacian_gram
    {P : B} (hP : P * P = P) (A C : B) :
    sheafLaplacian0 P (coneMinus P C) (conePlus P A) =
      star (genJ P A C) * genJ P A C := by
  have hCob : sheafCoboundary0 P (coneMinus P C) (conePlus P A) =
      -genJ P A C := by
    unfold sheafCoboundary0
    peirce_nf hP
  unfold sheafLaplacian0
  rw [hCob, star_neg, neg_mul_neg]

/-- The longitudinal Hopf coordinate and parity-twisted metric are the
corresponding Peirce operators. `sheafCurvature2` is deliberately not used:
its owner definition is an ordered product, not a commutator. -/
theorem rosetta_chiral_curvature_hopf
    {P : B} (hP : P * P = P) (hPs : star P = P) (A C : B) :
    hopfCoordZ (conePlus P A) (coneMinus P (star A)) = genSig P A (star A) ∧
    invS P * genV P A C = genSig P A C := by
  refine ⟨?_, ?_⟩
  · exact (operator_hopf_coordinate_identities_and_peirce_evaluations
      hP hPs (conePlus P A) (coneMinus P (star A)) A).2.2.2.2.2.1
  · peirce_nf hP

omit [StarRing B] in
/-- The logistic variance, cohomology complement, and Zorn quadratic norm
represent the same idempotency defect. -/
theorem rosetta_defect_unification {P : B} (hP : P * P = P) (A C : B) :
    NonCommutativeItFromBitLogisticPoset.logisticBitVariance P A C =
        -NonCommutativeOperatorTimePoset.idemDefect (genV P A C) ∧
    -(NonCommutativeItFromBitLogisticPoset.cohomologyProj P A C * genV P A C) =
        NonCommutativeOperatorTimePoset.idemDefect (genV P A C) ∧
    zornNorm P (genV P A C + genPhi P A C) =
        NonCommutativeOperatorTimePoset.idemDefect (genV P A C) := by
  rcases NonCommutativeItFromBitLogisticPoset.five_way_full_circle_unification_identity
      hP A C with ⟨hVar, _, hCoh, hZorn, _⟩
  exact ⟨by simpa using congrArg Neg.neg hVar, hCoh, hZorn⟩

omit [StarRing B] in
/-- The two chiral supports recover their own ordered squares from `V ± Σ`. -/
theorem rosetta_chiral_support_recovery {P : B} (hP : P * P = P) (A C : B) :
    (genV P A C + genSig P A C) * genV P A C =
        (2 : ℤ) • (qgtPlus P A C * qgtPlus P A C) ∧
    (genV P A C - genSig P A C) * genV P A C =
        (2 : ℤ) • (qgtMinus P A C * qgtMinus P A C) := by
  constructor <;>
    (simp only [genV, genSig, anticomm, comm, qgtPlus, qgtMinus]; peirce_nf hP)

/-! ### Master synthesis -/

/-- D₄₁ synthesis of verified metric, curvature, defect, and return operators.
Every component is an equality in the same possibly noncommutative ring. -/
theorem stage_D41_geometry_physics_information_operator_synthesis
    {P : B} (hP : P * P = P) (hPs : star P = P)
    (A C X X₁ X₂ Y₁ Y₂ : B) :
    1 - bergmanOp P A C 1 = genV P A C ∧
    operatorCrossRatio P A 0 C 0 = 1 - bergmanOp P A C 1 ∧
    operatorCrossRatio P (X₁ + A) (X₂ + A) (Y₁ + C) (Y₂ + C) =
      operatorCrossRatio P X₁ X₂ Y₁ Y₂ ∧
    (invS P + genPhi P A C) * (invS P + genPhi P A C) = 1 + genV P A C ∧
    hodgeLaplacianPhi P A C X =
      (2 : ℤ) • (genV P A C * X + X * genV P A C) ∧
    (1 + conePlus P A) * (1 - conePlus P A) = 1 ∧
    (1 - conePlus P A) * (1 + conePlus P A) = 1 ∧
    conjPlus P A P = P - conePlus P A ∧
    conjPlus P A (conjPlusInv P A X) = X ∧
    sheafLaplacian0 P (coneMinus P C) (conePlus P A) =
      star (genJ P A C) * genJ P A C ∧
    sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) = genV P A (star A) ∧
    magnetAdj P A * magnetAdj P A = genV P A (star A) ∧
    magnetAdj P A = genPhi P A (star A) ∧
    genJ P A (star A) * invS P = -genPhi P A (star A) ∧
    hopfCoordZ (conePlus P A) (coneMinus P (star A)) = genSig P A (star A) ∧
    invS P * genV P A C = genSig P A C ∧
    NonCommutativeItFromBitLogisticPoset.logisticBitVariance P A C =
      -NonCommutativeOperatorTimePoset.idemDefect (genV P A C) ∧
    zornNorm P (genV P A C + genPhi P A C) =
      NonCommutativeOperatorTimePoset.idemDefect (genV P A C) ∧
    (genV P A C + genSig P A C) * genV P A C =
      (2 : ℤ) • (qgtPlus P A C * qgtPlus P A C) ∧
    (genV P A C - genSig P A C) * genV P A C =
      (2 : ℤ) • (qgtMinus P A C * qgtMinus P A C) ∧
    (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) +
      kantorG0 P A C (kantorG0 P A C X) = genV P A C * X * genV P A C ∧
    kantorG0 P A C (kantorG0 P A C X) -
      (kantorGp2 P A (kantorGm2 P C X) + kantorGm2 P C (kantorGp2 P A X)) =
      genSig P A C * X * genSig P A C := by
  rcases rosetta_sheaf_and_magnetic_metric hP hPs A with ⟨hSheaf, hMag⟩
  have hGram := rosetta_sheaf_laplacian_gram hP A C
  rcases rosetta_chiral_curvature_hopf hP hPs A C with ⟨hHopf, hSV⟩
  rcases rosetta_defect_unification hP A C with ⟨hVar, _, hZorn⟩
  rcases rosetta_chiral_support_recovery hP A C with ⟨hPlus, hMinus⟩
  rcases archetype_A60_bilateral_support_reconstruction hP A C X with
    ⟨hKPlus, hKMinus⟩
  rcases archetype_A12_nilpotent_conjugation_group hP A 0 0 0 X with
    ⟨_, _, hConjInv, _, _, _, _, _, hChart, _, _, _⟩
  rcases archetype_A22_hua_distance_and_cross_ratio hP A C 0 0 A 0 C 0 with
    ⟨_, _, hCross, _, _, _⟩
  rcases archetype_A22_hua_distance_and_cross_ratio hP A C 0 0 X₁ X₂ Y₁ Y₂ with
    ⟨_, _, _, hCrossTranslate, _, _⟩
  have hMagJ : magnetAdj P A = invS P * genJ P A (star A) :=
    (digrac_flow_imbalance_and_magnet_laplacian
      (P := P) hPs hP 0 A 0).2.2.2.2.2.2.1
  have hSJ : invS P * genJ P A (star A) = genPhi P A (star A) := by
    peirce_nf hP
  have hJS : genJ P A (star A) * invS P = -genPhi P A (star A) := by
    peirce_nf hP
  exact ⟨rosetta_bergman_metric hP A C,
    hCross.trans (rosetta_bergman_metric hP A C).symm,
    hCrossTranslate,
    rosetta_bogoliubov_metric hP A C,
    hodgeLaplacianPhi_eq hP A C X,
    by peirce_nf hP, by peirce_nf hP, hChart, hConjInv,
    hGram, hSheaf, hMag, hMagJ.trans hSJ, hJS, hHopf, hSV, hVar, hZorn, hPlus, hMinus,
    hKPlus, hKMinus⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine

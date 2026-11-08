/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionFureyOperatorLift
import InfoGeometry.OperatorAlgebra.PeirceBdGFiveGradeBridge

/-!
# Split-octonion associator readout in the BdG five-grade anomaly

The native split-octonion carrier is nonassociative, so its left and right
regular maps need not commute.  The root-frame pair already owned by the
Furey operator lift has a nonzero mixed commutator, detected on `rootPlus 1`
as `lUnit`.  This module transports that exact readout to the positive
extreme grade of the associative BdG endomorphism matrix. Andreev conjugation
negates the full anomaly, so the particle and hole contributions cancel; the
reflected positive-grade operator is also identified with the negative
lower-grade component on the probe.

The five-grade decomposition here is the BdG chiral grading on matrices of
endomorphisms.  It is not identified with the separate circular `Z₃` grading
of the split-octonion carrier.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SplitOctonionBdGAnomalyReflection

open InfoGeometry.Lie.SplitOctonionFureyOperatorLift
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading
open InfoGeometry.Lie.SplitOctonionCircularZ3Grading
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.OperatorAlgebra.SplitOctonionMultiplicationOperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceBdGFiveGradeBridge
open InfoGeometry.Physics
open InfoGeometry.Physics.Algebra

abbrev BdGEnd := BdGBlock InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ

/-- The concrete Furey root-frame associator is the matrix coefficient of the
positive extreme BdG grade.  The hole-reflected input produces its negative,
so the two measured outputs cancel exactly.  The first clause also certifies
that the positive-grade component itself is nonzero. -/
theorem root_frame_associator_generates_andreev_cancelled_bdG_grade :
    let D : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ := leftRegular (rootPlus 0)
    let M : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ := rightRegular (rootPlus 2)
    let E : BdGEnd := massiveBdGCommutatorAnomaly D M
    let ePos := fiveGradeProjector
      (chiralGrading (A := InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)) .posTwo E
    ((Matrix.mulVec ePos ![0, (1 : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)]) 0)
      (rootPlus 1) = lUnit ∧
    ePos ≠ 0 ∧
    ((Matrix.mulVec (E + andreevSwap * E * andreevSwap)
      ![0, (1 : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)]) 0)
        (rootPlus 1) = 0 ∧
    (Matrix.mulVec (andreevSwap * ePos * andreevSwap)
      ![(1 : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ), 0] 1)
        (rootPlus 1) = lUnit := by
  dsimp
  let D : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ := leftRegular (rootPlus 0)
  let M : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ := rightRegular (rootPlus 2)
  let E : BdGEnd := massiveBdGCommutatorAnomaly D M
  let ePos := fiveGradeProjector
    (chiralGrading (A := InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)) .posTwo E
  let eNeg := fiveGradeProjector
    (chiralGrading (A := InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)) .negTwo E
  have hGrades := massiveBdG_chiral_anomaly_exact_fiveGrade_components D M
  rcases hGrades with ⟨hPos, hNeg, _, _, _⟩
  have hRoot := root_frame_regular_commutator_is_split_axis
  have hReadout : (D * M - M * D) (rootPlus 1) = lUnit := by
    change (leftRegular (rootPlus 0) * rightRegular (rootPlus 2) -
      rightRegular (rootPlus 2) * leftRegular (rootPlus 0)) (rootPlus 1) = lUnit
    exact hRoot
  have hPlus : ePos = !![0, D * M - M * D; 0, 0] := by
    dsimp [ePos, E]
    exact hPos
  have hMinus : eNeg = !![0, 0; M * D - D * M, 0] := by
    dsimp [eNeg, E]
    exact hNeg
  have hPlusReadout :
      ((Matrix.mulVec ePos
        ![0, (1 : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)]) 0)
        (rootPlus 1) = lUnit := by
    rw [hPlus]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hReadout]
  have hPlusNonzero : ePos ≠ 0 := by
    intro hz
    have hz' := congrArg
      (fun T : BdGEnd =>
        ((Matrix.mulVec T ![0, (1 : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)]) 0)
          (rootPlus 1)) hz
    rw [hPlusReadout] at hz'
    simp at hz'
    have hl : lUnit ≠ (0 : InfoGeometry.Canonical.ZornMatrix ℝ) := by
      intro h
      have hx := congrArg (fun x : InfoGeometry.Canonical.ZornMatrix ℝ => x.x 0) h
      norm_num [lUnit] at hx
    exact hl hz'
  have hCancel : E + andreevSwap * E * andreevSwap = 0 := by
    rw [andreev_reflect_mass_commutator_anomaly D M]
    exact add_neg_cancel _
  have hCancelReadout :
      ((Matrix.mulVec (E + andreevSwap * E * andreevSwap)
        ![0, (1 : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)]) 0)
          (rootPlus 1) = 0 := by
    rw [hCancel]
    simp
  have hReflected :
      andreevSwap * ePos * andreevSwap = -eNeg := by
    exact (andreev_reflect_chiral_anomaly_grade_components D M).1
  have hReflectedReadout :
          (Matrix.mulVec (andreevSwap * ePos * andreevSwap)
            ![(1 : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ), 0] 1)
          (rootPlus 1) = lUnit := by
    rw [hReflected, hMinus]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hReadout]
  exact ⟨hPlusReadout, hPlusNonzero, hCancelReadout, hReflectedReadout⟩

/-- The BdG `+2` component does not merely detect a nonzero split-octonion
output: its canonical root-frame probe lands in the existing circular grade
zero submodule. This is the carrier-level bridge between the BdG five-grade
decomposition and the split-octonion circular `Z₃` grading. -/
theorem root_frame_BdG_extreme_grade_readout_mem_zero_circular_grade :
    ((Matrix.mulVec
      (fiveGradeProjector
        (chiralGrading (A := InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)) .posTwo
        (massiveBdGCommutatorAnomaly
          (leftRegular (rootPlus 0)) (rightRegular (rootPlus 2))))
      ![0, (1 : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)]) 0)
        (rootPlus 1) ∈ circularGradeSubmodule 0 := by
  have hReadout :
      ((Matrix.mulVec
        (fiveGradeProjector
          (chiralGrading (A := InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)) .posTwo
          (massiveBdGCommutatorAnomaly
            (leftRegular (rootPlus 0)) (rightRegular (rootPlus 2))))
        ![0, (1 : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)]) 0)
          (rootPlus 1) = lUnit := by
    simpa only [] using root_frame_associator_generates_andreev_cancelled_bdG_grade.1
  rw [hReadout]
  rw [← root_frame_regular_commutator_is_split_axis]
  exact root_frame_regular_commutator_output_mem_zero_grade

/-- The two extreme BdG grades of the lifted split-octonion mixed
commutator vanish exactly when the corresponding associator vanishes on the
whole split-octonion carrier. Thus the five-grade obstruction is precisely
the failure of the regular left and right actions to commute, with no choice
of a special test vector built into the criterion. -/
theorem split_octonion_associator_iff_BdG_extreme_grades_vanish
    (x z : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.CZ) :
    (fiveGradeProjector
        (chiralGrading
          (A := InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)) .posTwo
        (massiveBdGCommutatorAnomaly (leftRegular x) (rightRegular z)) = 0 ∧
      fiveGradeProjector
        (chiralGrading
          (A := InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)) .negTwo
        (massiveBdGCommutatorAnomaly (leftRegular x) (rightRegular z)) = 0) ↔
      ∀ y : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.CZ,
        splitAssociator x y z = 0 := by
  classical
  let D : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ := leftRegular x
  let M : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ := rightRegular z
  have hGradeCriterion := massiveBdG_noncommutation_has_both_extreme_grades D M
  have hAssociatorCriterion := regular_operators_commute_iff_associator_vanishes x z
  constructor
  · rintro ⟨hPosZero, _⟩
    have hDM : D * M = M * D := by
      by_contra hNotDM
      have hGrades := hGradeCriterion.mpr hNotDM
      exact hGrades.1 (hPosZero)
    exact hAssociatorCriterion.mp (by simpa [D, M] using hDM)
  · intro hAssoc
    have hDM : D * M = M * D := by
      simpa [D, M] using hAssociatorCriterion.mpr hAssoc
    have hAnomalyZero : massiveBdGCommutatorAnomaly D M = 0 :=
      (massiveBdGCommutatorAnomaly_eq_zero_iff_commute D M).2 hDM
    constructor
    · rw [hAnomalyZero]
      simp
    · rw [hAnomalyZero]
      simp

/-- A native split-octonion Cartan weight is recorded directly in the two
extreme BdG grades of the interaction anomaly. The upper block carries the
Cartan-weighted chiral root operator; the lower block carries its negative,
as forced by reversing the commutator. -/
theorem axialCartan_root_operator_BdG_grade_components
    (k : Fin 3 → ℝ) (hk : ∑ j, k j = 0) (i : Fin 3) :
    fiveGradeProjector
        (chiralGrading
          (A := InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)) .posTwo
        (massiveBdGCommutatorAnomaly
          (InfoGeometry.Lie.SplitOctonionAxialCartanDerivation.axialCartanEnd k)
          (leftRegular
            (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis i))) =
      !![0, k i • leftRegular
            (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis i);
        0, 0] ∧
    fiveGradeProjector
        (chiralGrading
          (A := InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)) .negTwo
        (massiveBdGCommutatorAnomaly
          (InfoGeometry.Lie.SplitOctonionAxialCartanDerivation.axialCartanEnd k)
          (leftRegular
            (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis i))) =
      !![0, 0;
        -(k i • leftRegular
            (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis i)), 0] := by
  let D : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ :=
    InfoGeometry.Lie.SplitOctonionAxialCartanDerivation.axialCartanEnd k
  let M : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ :=
    leftRegular
      (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis i)
  have hWeight : D * M - M * D = k i • M := by
    simpa [D, M, LieRing.of_associative_ring_bracket] using
      InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.axialCartan_upper_eigenoperator
        k hk i
  have hReverse : M * D - D * M = -(k i • M) := by
    calc
      M * D - D * M = -(D * M - M * D) := by noncomm_ring
      _ = -(k i • M) := congrArg Neg.neg hWeight
  rcases massiveBdG_chiral_anomaly_exact_fiveGrade_components D M with
    ⟨hPos, hNeg, _, _, _⟩
  constructor
  · rw [hPos, hWeight]
  · rw [hNeg, hReverse]

/-- Every generator in the repository's native fourteen-dimensional split-
`G₂` derivation basis acts on a left-regular split-octonion operator through
the `+2` and `-2` BdG grades. The graded interaction is exactly the left
regular image of the generator's action on the state, with opposite signs in
the two particle-hole blocks. -/
theorem splitG2_basis_BdG_grade_components
    (i : Fin 14) (x : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.CZ) :
    fiveGradeProjector
        (chiralGrading
          (A := InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)) .posTwo
        (massiveBdGCommutatorAnomaly
          (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i)
          (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x)) =
      !![0, InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
          ((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i).1 x);
        0, 0] ∧
    fiveGradeProjector
        (chiralGrading
          (A := InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ)) .negTwo
        (massiveBdGCommutatorAnomaly
          (InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i)
          (InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x)) =
      !![0, 0;
        -InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
          ((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i).1 x), 0] := by
  let D : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ :=
    InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i
  let M : InfoGeometry.Lie.SplitOctonionFureyOperatorLift.EndCZ :=
    InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular x
  have hAction :=
    InfoGeometry.Lie.SplitOctonionFureyOperatorLift.casG2RootGenerator_leftRegular_commutator
      i x
  have hComm : D * M - M * D = InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
      ((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i).1 x) := by
    simpa [D, M, LieRing.of_associative_ring_bracket] using hAction
  have hReverse : M * D - D * M = -InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading.leftRegular
      ((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i).1 x) := by
    calc
      M * D - D * M = -(D * M - M * D) := by noncomm_ring
      _ = -leftRegular
          ((InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivationBasis i).1 x) :=
        congrArg Neg.neg hComm
  rcases massiveBdG_chiral_anomaly_exact_fiveGrade_components D M with
    ⟨hPos, hNeg, _, _, _⟩
  exact ⟨by rw [hPos, hComm], by rw [hNeg, hReverse]⟩

end InfoGeometry.OperatorAlgebra.SplitOctonionBdGAnomalyReflection

end

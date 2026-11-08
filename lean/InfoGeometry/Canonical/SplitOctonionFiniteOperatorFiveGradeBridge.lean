/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.SplitOctonionLeftMultiplicationBridge
import InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis
import InfoGeometry.Lie.SplitOctonionCircularZ3Grading

/-!
# Finite split-octonion operators in the five-graded endomorphism algebra

The canonical Zorn carrier has two existing operator realizations: left
multiplication on its intrinsic carrier and the corresponding `8 × 8` real
operator on `Fin 8 → ℝ`. Conjugation by the repository's coordinate
equivalence identifies their multiplication defects. This transports the
explicit finite operator defect into the already-proved five-grade
decomposition without identifying Zorn multiplication with associative
endomorphism composition.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionFiniteOperatorFiveGradeBridge

open InfoGeometry.OperatorAlgebra.SplitOctonionLeftMultiplicationBridge
open InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
open InfoGeometry.Canonical.ZornFiveGradeCurvatureBianchiSynthesis
open InfoGeometry.Lie.SplitOctonionFiveGradeOperatorBridge
open InfoGeometry.Lie.SplitOctonionPeirceFermionParityBridge
open InfoGeometry.OperatorAlgebra.SplitOctonionLoxodromic
open InfoGeometry.Algebra.ZornLeftCAR
open InfoGeometry.Core.TripotentAdjoint
open InfoGeometry.Physics.Algebra
open InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionCircularZ3Grading
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The coordinate equivalence identifies endomorphisms on the eight real
coordinates with endomorphisms of the canonical Zorn carrier. -/
def finiteOperatorEndEquiv :
    Module.End ℝ State ≃ₐ[ℝ]
      InfoGeometry.Lie.SplitOctonionPeirceFermionParityBridge.CarrierEnd :=
  AlgEquiv.ofLinearEquiv
    (coordLE.symm.conj)
    (by
      apply LinearMap.ext
      intro X
      simp [LinearEquiv.conj_apply])
    (fun S T => by
      apply LinearMap.ext
      intro X
      simp [LinearEquiv.conj_apply, Module.End.mul_apply])

/-- Under the coordinate conjugation, the finite `Fin 8` left action is the
canonical left-multiplication map on `ZornMatrix ℝ`. -/
theorem finiteOperatorEndEquiv_leftMul
    (X : InfoGeometry.OperatorAlgebra.SplitOctonionLeftMultiplicationBridge.Carrier) :
    finiteOperatorEndEquiv (leftMulLinearGeneral X) =
      canonicalLeftMultiplicationMap X := by
  apply LinearMap.ext
  intro Y
  change coordLE.symm (leftMulLinearGeneral X (coordLE Y)) = X * Y
  simp [leftMulLinearGeneral,
    InfoGeometry.OperatorAlgebra.SplitOctonionLoxodromic.zMulLinear]

/-- The canonical finite-coordinate conjugation transports the full
left-multiplication composition defect, with its ordered product, to the
associator defect used by the five-grade owner. -/
theorem finiteOperatorEndEquiv_compDefect
    (X Y : InfoGeometry.OperatorAlgebra.SplitOctonionLeftMultiplicationBridge.Carrier) :
    finiteOperatorEndEquiv (leftMulCompDefect X Y) =
      -canonicalMultiplicationDefect X Y := by
  have hmul : finiteOperatorEndEquiv
      ((leftMulLinearGeneral X).comp (leftMulLinearGeneral Y)) =
      finiteOperatorEndEquiv (leftMulLinearGeneral X) *
        finiteOperatorEndEquiv (leftMulLinearGeneral Y) :=
    finiteOperatorEndEquiv.map_mul _ _
  change finiteOperatorEndEquiv
      ((leftMulLinearGeneral X).comp (leftMulLinearGeneral Y) -
        leftMulLinearGeneral (X * Y)) = _
  calc
    finiteOperatorEndEquiv
        ((leftMulLinearGeneral X).comp (leftMulLinearGeneral Y) -
          leftMulLinearGeneral (X * Y)) =
        finiteOperatorEndEquiv ((leftMulLinearGeneral X).comp
          (leftMulLinearGeneral Y)) - finiteOperatorEndEquiv (leftMulLinearGeneral (X * Y)) :=
      finiteOperatorEndEquiv.toLinearEquiv.map_sub _ _
    _ = finiteOperatorEndEquiv (leftMulLinearGeneral X) *
          finiteOperatorEndEquiv (leftMulLinearGeneral Y) -
          finiteOperatorEndEquiv (leftMulLinearGeneral (X * Y)) := by
      rw [hmul]
    _ = -canonicalMultiplicationDefect X Y := by
      rw [finiteOperatorEndEquiv_leftMul, finiteOperatorEndEquiv_leftMul,
        finiteOperatorEndEquiv_leftMul]
      unfold canonicalMultiplicationDefect
      abel

/-- The explicit nonzero defect from the finite `8 × 8` operator action has a
nonzero five-grade coordinate tuple after transport to the canonical
endomorphism algebra. -/
theorem finite_operator_associator_defect_has_nonzero_five_grade_readout :
    fiveGradeDecomposeLinear peirceDefectOperator
      (finiteOperatorEndEquiv
        (leftMulCompDefect
          (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
          (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1))) ≠ 0 := by
  rw [finiteOperatorEndEquiv_compDefect]
  simpa using (neg_ne_zero.mpr canonicalMultiplicationDefect_fiveGradeCoordinates_ne_zero)

set_option maxHeartbeats 800000 in
/-- The negative-one five-grade component of the finite root-pair associator
defect sends the third positive circular root to the nonzero split axis. This
identifies an actual adjoint-grade component, not only a nonzero grade tuple. -/
theorem root_defect_negOne_readout :
    (fiveGradeProjector peirceDefectOperator .negOne
      (finiteOperatorEndEquiv (leftMulCompDefect (rootPlus 0) (rootPlus 1))))
      (rootPlus 2) = lUnit := by
  have hD : finiteOperatorEndEquiv (leftMulCompDefect (rootPlus 0) (rootPlus 1))
      (rootPlus 2) = lUnit := by
    change coordLE.symm (leftMulCompDefect (rootPlus 0) (rootPlus 1)
      (coordLE (rootPlus 2))) = lUnit
    rw [leftMulCompDefect_apply_coord, map_neg, coordLE.symm_apply_apply,
      rootPlus_associator_zero_one_two, neg_sub, uPlus_sub_uMinus]
  have hp : peirceDefectOperator (rootPlus 2) = rootPlus 2 := by
    change axialGrading (rootPlus 2) = rootPlus 2
    rw [axialGrading, LinearMap.smul_apply, ellCommutator_rootPlus]
    module
  have hz : peirceDefectOperator lUnit = 0 := by
    change axialGrading lUnit = 0
    rw [← uPlus_sub_uMinus, axialGrading, LinearMap.smul_apply, map_sub,
      ellCommutator_uPlus, ellCommutator_uMinus]
    simp only [sub_self, smul_zero]
  have hpos : projPos peirceDefectOperator (rootPlus 2) = rootPlus 2 := by
    simp only [projPos, LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply, hp]
    module
  have hzero : projZero peirceDefectOperator (rootPlus 2) = 0 := by
    simp only [projZero, LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply, hp,
      sub_self]
  have hzeroOut : projZero peirceDefectOperator lUnit = lUnit := by
    simp only [projZero, LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply, hz,
      map_zero, sub_zero]
  simp only [fiveGradeProjector_negOne, gradeNegOneProjector, LinearMap.add_apply,
    jointPeirceProjector_apply, peirceProjector_zero, peirceProjector_pos,
    peirceProjector_neg, Module.End.mul_apply, hpos, hzero, hD, map_zero, hzeroOut, add_zero]

/-- The negative-one component of this finite root-pair defect is nonzero. -/
theorem root_defect_negOne_ne_zero :
    fiveGradeProjector peirceDefectOperator .negOne
      (finiteOperatorEndEquiv (leftMulCompDefect (rootPlus 0) (rootPlus 1))) ≠ 0 := by
  intro h
  have heval := congrArg (fun T : CarrierEnd => T (rootPlus 2)) h
  rw [root_defect_negOne_readout] at heval
  have hne : lUnit ≠ (0 : InfoGeometry.Canonical.ZornMatrix ℝ) := by
    intro h
    have hx := congrArg (fun x : InfoGeometry.Canonical.ZornMatrix ℝ => x.x 0) h
    norm_num [lUnit] at hx
  exact hne (by simpa using heval)

set_option maxHeartbeats 800000 in
/-- The same grade `-1` component maps the split axis to the third negative
root. Together with `root_defect_negOne_readout` this exhibits a nontrivial
three-step operator chain on the genuine split-octonion carrier. -/
theorem root_defect_negOne_axis_readout :
    (fiveGradeProjector peirceDefectOperator .negOne
      (finiteOperatorEndEquiv (leftMulCompDefect (rootPlus 0) (rootPlus 1))))
      lUnit = (-2 : ℝ) • rootMinus 2 := by
  have hd : finiteOperatorEndEquiv (leftMulCompDefect (rootPlus 0) (rootPlus 1)) lUnit =
      (-2 : ℝ) • rootMinus 2 := by
    change coordLE.symm (leftMulCompDefect (rootPlus 0) (rootPlus 1) (coordLE lUnit)) = _
    rw [leftMulCompDefect_apply_coord, map_neg, coordLE.symm_apply_apply,
      rootPlus_zero_mul_rootPlus_one, rootMinus_mul_lUnit, rootPlus_mul_lUnit]
    have hm : rootPlus 0 * (-rootPlus 1) = -(rootPlus 0 * rootPlus 1) := by
      simpa using InfoGeometry.Canonical.ZornClifford.mul_smul' (-1 : ℝ) (rootPlus 0) (rootPlus 1)
    rw [hm, rootPlus_zero_mul_rootPlus_one]
    module
  have hz : peirceDefectOperator lUnit = 0 := by
    change axialGrading lUnit = 0
    rw [← uPlus_sub_uMinus, axialGrading, LinearMap.smul_apply, map_sub,
      ellCommutator_uPlus, ellCommutator_uMinus]
    simp only [sub_self, smul_zero]
  have hn : peirceDefectOperator (rootMinus 2) = -(rootMinus 2) := by
    change axialGrading (rootMinus 2) = -(rootMinus 2)
    rw [axialGrading, LinearMap.smul_apply, ellCommutator_rootMinus]
    module
  have hzpos : projPos peirceDefectOperator lUnit = 0 := by
    simp only [projPos, LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply, hz,
      map_zero, add_zero, smul_zero]
  have hzzero : projZero peirceDefectOperator lUnit = lUnit := by
    simp only [projZero, LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply, hz,
      map_zero, sub_zero]
  have hnneg : projNeg peirceDefectOperator (rootMinus 2) = rootMinus 2 := by
    simp only [projNeg, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply,
      hn, map_neg, neg_neg]
    module
  simp only [fiveGradeProjector_negOne, gradeNegOneProjector, LinearMap.add_apply,
    jointPeirceProjector_apply, peirceProjector_zero, peirceProjector_pos,
    peirceProjector_neg, Module.End.mul_apply, hzpos, hzzero, map_zero, hd,
    map_smul, hnneg, zero_add]

/-- The square of the grade `-1` component is genuinely nonzero. -/
theorem root_defect_negOne_square_ne_zero :
    (fiveGradeProjector peirceDefectOperator .negOne
      (finiteOperatorEndEquiv (leftMulCompDefect (rootPlus 0) (rootPlus 1)))) ^ 2 ≠ 0 := by
  intro h
  have heval := congrArg (fun T : CarrierEnd => T (rootPlus 2)) h
  simp only [pow_two, Module.End.mul_apply, LinearMap.zero_apply,
    root_defect_negOne_readout, root_defect_negOne_axis_readout] at heval
  have hminus : rootMinus 2 ≠ 0 := rootMinus_two_ne_zero
  exact (smul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) hminus) heval

/-- Its cube vanishes because the five-grading has no adjoint weight `-3`. -/
theorem root_defect_negOne_cube_eq_zero :
    (fiveGradeProjector peirceDefectOperator .negOne
      (finiteOperatorEndEquiv (leftMulCompDefect (rootPlus 0) (rootPlus 1)))) ^ 3 = 0 := by
  let Q := fiveGradeProjector peirceDefectOperator .negOne
    (finiteOperatorEndEquiv (leftMulCompDefect (rootPlus 0) (rootPlus 1)))
  have hQ : Q ∈ fiveGradeRange peirceDefectOperator .negOne := ⟨_, rfl⟩
  have hQ2 : Q * Q ∈ fiveGradeRange peirceDefectOperator .negTwo :=
    zornFiveGrade_mul_mem (by decide) hQ hQ
  have hQ' : Q ∈ (LieAlgebra.ad ℝ CarrierEnd peirceDefectOperator).eigenspace (-1 : ℝ) := by
    rw [zornFiveGradeRange_eq_adjointEigenspace] at hQ
    simpa [fiveGradeValue] using hQ
  have hQ2' : Q * Q ∈ (LieAlgebra.ad ℝ CarrierEnd peirceDefectOperator).eigenspace (-2 : ℝ) := by
    rw [zornFiveGradeRange_eq_adjointEigenspace] at hQ2
    simpa [fiveGradeValue] using hQ2
  have hnot : (-2 : ℝ) + (-1 : ℝ) ∉
      Set.range (fun k : FiveGrade => (fiveGradeValue k : ℝ)) := by
    rintro ⟨k, hk⟩
    cases k <;> norm_num [fiveGradeValue] at hk
  have hzero : (Q * Q) * Q = 0 :=
    zornFiveGrade_mul_eq_zero_of_weight_not_mem hQ2' hQ' hnot
  simpa [pow_succ, pow_two, Q] using hzero

/-- The terminal negative root of the concrete grade `-1` operator chain is
annihilated. This follows from the checked cube-zero law and the two readouts. -/
theorem root_defect_negOne_bottom_zero :
    (fiveGradeProjector peirceDefectOperator .negOne
      (finiteOperatorEndEquiv (leftMulCompDefect (rootPlus 0) (rootPlus 1))))
      (rootMinus 2) = 0 := by
  have h := congrArg (fun T : CarrierEnd => T (rootPlus 2)) root_defect_negOne_cube_eq_zero
  simp only [pow_succ, Module.End.mul_apply, LinearMap.zero_apply,
    root_defect_negOne_readout, root_defect_negOne_axis_readout, map_smul] at h
  exact (smul_eq_zero.mp h).resolve_left (by norm_num : (-2 : ℝ) ≠ 0)

set_option maxHeartbeats 800000 in
/-- The three vectors in the defect chain are linearly independent: they are
nonzero eigenvectors of the native Peirce operator at distinct weights. -/
theorem root_defect_chain_linearIndependent :
    LinearIndependent ℝ ![rootPlus 2, lUnit, rootMinus 2] := by
  apply Module.End.eigenvectors_linearIndependent' peirceDefectOperator ![1, 0, -1]
  · intro i j h
    fin_cases i <;> fin_cases j <;> norm_num at h <;> rfl
  · intro i
    fin_cases i
    · constructor
      · rw [Module.End.mem_eigenspace_iff]
        change axialGrading (rootPlus 2) = (1 : ℝ) • rootPlus 2
        rw [one_smul, axialGrading, LinearMap.smul_apply, ellCommutator_rootPlus]
        module
      · change rootPlus 2 ≠ 0
        rw [← circularPeirceBasis_three]
        exact circularPeirceBasis_ne_zero 3
    · constructor
      · rw [Module.End.mem_eigenspace_iff]
        change axialGrading lUnit = (0 : ℝ) • lUnit
        rw [← uPlus_sub_uMinus, axialGrading, LinearMap.smul_apply, map_sub,
          ellCommutator_uPlus, ellCommutator_uMinus]
        simp only [sub_self, smul_zero, zero_smul]
      · intro h
        have hx := congrArg (fun x : InfoGeometry.Canonical.ZornMatrix ℝ => x.x 0) h
        norm_num [lUnit] at hx
    · constructor
      · rw [Module.End.mem_eigenspace_iff]
        change axialGrading (rootMinus 2) = (-1 : ℝ) • rootMinus 2
        rw [axialGrading, LinearMap.smul_apply, ellCommutator_rootMinus]
        module
      · exact rootMinus_two_ne_zero

private theorem span_invariant_of_three_chain {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : Module.End ℝ E) (x y z : E) (c : ℝ)
    (hx : f x = y) (hy : f y = c • z) (hz : f z = 0) :
    Submodule.map f (Submodule.span ℝ (Set.range (![x, y, z] : Fin 3 → E))) ≤
      Submodule.span ℝ (Set.range (![x, y, z] : Fin 3 → E)) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  fin_cases i
  · change f x ∈ Submodule.span ℝ (Set.range (![x, y, z] : Fin 3 → E))
    rw [hx]
    exact Submodule.subset_span ⟨1, rfl⟩
  · change f y ∈ Submodule.span ℝ (Set.range (![x, y, z] : Fin 3 → E))
    rw [hy]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩)
  · change f z ∈ Submodule.span ℝ (Set.range (![x, y, z] : Fin 3 → E))
    rw [hz]
    exact Submodule.zero_mem _

/-- The actual grade `-1` Zorn defect preserves the span of its three-step
root-axis-root chain. -/
theorem root_defect_chain_span_invariant :
    Submodule.map
      (fiveGradeProjector peirceDefectOperator .negOne
        (finiteOperatorEndEquiv (leftMulCompDefect (rootPlus 0) (rootPlus 1))))
      (Submodule.span ℝ (Set.range (![rootPlus 2, lUnit, rootMinus 2] :
        Fin 3 → InfoGeometry.Canonical.ZornMatrix ℝ))) ≤
    Submodule.span ℝ (Set.range (![rootPlus 2, lUnit, rootMinus 2] :
      Fin 3 → InfoGeometry.Canonical.ZornMatrix ℝ)) := by
  exact span_invariant_of_three_chain _ _ _ _ (-2) root_defect_negOne_readout
    root_defect_negOne_axis_readout root_defect_negOne_bottom_zero

/-- The invariant root-axis-root span has real dimension exactly three. -/
theorem root_defect_chain_span_finrank :
    Module.finrank ℝ
      (Submodule.span ℝ (Set.range (![rootPlus 2, lUnit, rootMinus 2] :
        Fin 3 → InfoGeometry.Canonical.ZornMatrix ℝ))) = 3 := by
  simpa using (finrank_span_eq_card root_defect_chain_linearIndependent)

/-- The concrete grade `-1` defect is an eigenvector of the actual Peirce
inner derivation, with weight `-1`. -/
theorem root_defect_negOne_commutator :
    peirceDefectOperator *
        (fiveGradeProjector peirceDefectOperator .negOne
          (finiteOperatorEndEquiv (leftMulCompDefect (rootPlus 0) (rootPlus 1)))) -
      (fiveGradeProjector peirceDefectOperator .negOne
          (finiteOperatorEndEquiv (leftMulCompDefect (rootPlus 0) (rootPlus 1)))) *
        peirceDefectOperator =
      -(fiveGradeProjector peirceDefectOperator .negOne
          (finiteOperatorEndEquiv (leftMulCompDefect (rootPlus 0) (rootPlus 1)))) := by
  let Q := fiveGradeProjector peirceDefectOperator .negOne
    (finiteOperatorEndEquiv (leftMulCompDefect (rootPlus 0) (rootPlus 1)))
  have h : Q ∈ fiveGradeRange peirceDefectOperator .negOne := ⟨_, rfl⟩
  rw [zornFiveGradeRange_eq_adjointEigenspace] at h
  rw [Module.End.mem_eigenspace_iff] at h
  change peirceDefectOperator * Q - Q * peirceDefectOperator = -Q
  simpa only [fiveGradeValue, LieAlgebra.ad_apply, Ring.lie_def, Int.cast_neg,
    Int.cast_one, neg_one_smul] using h

/-- The transported finite operator defect is a new five-grade Lie generator:
it lies in the Lie span of the canonical left actions but outside their
linear range. -/
theorem finite_operator_associator_defect_generates_new_grade :
    finiteOperatorEndEquiv
        (leftMulCompDefect
          (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
          (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1)) ∈
      LieSubalgebra.lieSpan ℝ CarrierEnd (Set.range canonicalLeftMultiplicationMap) ∧
    finiteOperatorEndEquiv
        (leftMulCompDefect
          (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 0)
          (InfoGeometry.Canonical.ZornMatrix.chiralUpperBasis (R := ℝ) 1)) ∉
      LinearMap.range canonicalLeftMultiplicationMap := by
  rw [finiteOperatorEndEquiv_compDefect]
  constructor
  · exact (LieSubalgebra.lieSpan ℝ CarrierEnd
      (Set.range canonicalLeftMultiplicationMap)).neg_mem
        (canonicalMultiplicationDefect_mem_lieSpan _ _)
  · intro hneg
    apply canonicalMultiplicationDefect_chiralUpper01_not_mem_left_range
    simpa using (LinearMap.range canonicalLeftMultiplicationMap).neg_mem hneg

end InfoGeometry.Canonical.SplitOctonionFiniteOperatorFiveGradeBridge

end

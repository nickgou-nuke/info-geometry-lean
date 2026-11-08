/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.InfinityTwistor
import InfoGeometry.Twistor.TwistorOperatorLift
import InfoGeometry.Twistor.PenroseTwistorDerivationTransport
import InfoGeometry.Lie.SplitOctonionCircularZ3Grading
import InfoGeometry.Lie.SplitOctonionFiveGradeOperatorBridge
import InfoGeometry.Core.TripotentEigenspaces
import InfoGeometry.Algebra.Zorn.CanonicalKantorOperators
import InfoGeometry.Lie.SplitOctonionEllKantorRankOne
import Mathlib.Algebra.Lie.OfAssociative

set_option maxHeartbeats 1000000

/-!
# Infinity radical inside the faithful Zorn operator lift

The degenerate infinity twistor has the first spinor sheet as its radical.
The existing real twistor-to-Zorn left-regular representation is faithful, so
this radical is identified exactly with the operator image of that sheet.
This bridge uses the existing carriers and does not identify the form with a
mass or curvature operator.
-/

namespace InfoGeometry.Twistor.InfinityTwistorOperatorLiftBridge

open InfoGeometry.Twistor.PenroseIncidence
open InfoGeometry.Twistor.InfinityTwistor
open InfoGeometry.Twistor.RealSplitOctonionCarrierBridge
open InfoGeometry.Twistor.ChiralTwistorPeirceSheets
open InfoGeometry.Twistor.TwistorZornDerivationTransport
open InfoGeometry.Twistor.TwistorOperatorLift
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.ZornLeftCAR
open InfoGeometry.Algebra.Zorn.CanonicalKantorOperators
open InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Lie.SplitOctonionCircularZ3Grading
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Core.TripotentAdjoint
open InfoGeometry.Physics.Algebra
open InfoGeometry.Twistor.PenroseTwistorDerivationTransport

abbrev CanonicalZorn := InfoGeometry.Canonical.ZornMatrix ℝ

/-- The same twistor carrier expressed in the canonical Zorn algebra. -/
noncomputable def twistorCanonicalZorn (z : Twistor4) : CanonicalZorn :=
  canonicalVectorEquiv.symm (twistorZornLinearMap z)

/-- The carrier map transports the actual twistor product to the canonical
nonassociative Zorn product. -/
theorem twistorCanonicalZorn_mul (z w : Twistor4) :
    twistorCanonicalZorn (twistorMul z w) =
      twistorCanonicalZorn z * twistorCanonicalZorn w := by
  unfold twistorCanonicalZorn
  rw [← canonicalVectorEquiv_symm_mul]
  exact congrArg canonicalVectorEquiv.symm (twistorZornLinearMap_mul z w)

/-- The Zorn associator is exactly the image of the parenthesization defect
in the twistor algebra. This retains the nonassociative term under transport. -/
theorem twistorCanonicalZorn_associator (z w v : Twistor4) :
    twistorZornLinearMap
        (twistorMul (twistorMul z w) v - twistorMul z (twistorMul w v)) =
      InfoGeometry.Algebra.ZornVectorMatrix.associator
        (twistorZornLinearMap z) (twistorZornLinearMap w)
        (twistorZornLinearMap v) := by
  rw [map_sub,
    twistorZornLinearMap_mul (twistorMul z w) v,
    twistorZornLinearMap_mul z (twistorMul w v),
    twistorZornLinearMap_mul z w,
    twistorZornLinearMap_mul w v]
  change InfoGeometry.Algebra.ZornVectorMatrix.sub
      (InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.mul
          (twistorZornLinearMap z) (twistorZornLinearMap w))
        (twistorZornLinearMap v))
      (InfoGeometry.Algebra.ZornVectorMatrix.mul
        (twistorZornLinearMap z)
        (InfoGeometry.Algebra.ZornVectorMatrix.mul
          (twistorZornLinearMap w) (twistorZornLinearMap v))) = _
  rfl

/-- The concrete Kantor triple operator is evaluated in the same full Zorn
algebra reached by the twistor lift; this identity preserves its ordered
conjugation and multiplication convention. -/
theorem twistorCanonicalZorn_kantorV (z w v : Twistor4) :
    canonicalVectorEquiv
        (InfoGeometry.Algebra.Zorn.CanonicalKantorOperators.V
          (twistorCanonicalZorn z) (twistorCanonicalZorn w)
          (twistorCanonicalZorn v)) =
      (InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.mul
          (twistorZornLinearMap z)
          (InfoGeometry.Algebra.ZornVectorMatrix.conj
            (twistorZornLinearMap w)))
        (twistorZornLinearMap v)) +
      (InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.mul
          (twistorZornLinearMap v)
          (InfoGeometry.Algebra.ZornVectorMatrix.conj
            (twistorZornLinearMap w)))
        (twistorZornLinearMap z)) -
      (InfoGeometry.Algebra.ZornVectorMatrix.mul
        (InfoGeometry.Algebra.ZornVectorMatrix.mul
          (twistorZornLinearMap v)
          (InfoGeometry.Algebra.ZornVectorMatrix.conj
            (twistorZornLinearMap z)))
        (twistorZornLinearMap w)) := by
  simp only [InfoGeometry.Algebra.Zorn.CanonicalKantorOperators.V,
    twistorCanonicalZorn, Equiv.apply_symm_apply,
    canonicalVectorEquiv_mul, canonicalVectorEquiv_add,
    canonicalVectorEquiv_sub,
    InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.canonicalVectorEquiv_canonicalConj]
  rfl

/-- Antisymmetrization defining the Kantor `K` operator commutes with the
twistor-to-Zorn transport. This keeps the concrete Kantor convention tied to
the native `V` product rather than introducing a second triple system. -/
theorem twistorCanonicalZorn_kantorK (z w v : Twistor4) :
    canonicalVectorEquiv
        (InfoGeometry.Algebra.Zorn.CanonicalKantorOperators.K
          (twistorCanonicalZorn z) (twistorCanonicalZorn w)
          (twistorCanonicalZorn v)) =
      canonicalVectorEquiv
          (InfoGeometry.Algebra.Zorn.CanonicalKantorOperators.V
            (twistorCanonicalZorn z) (twistorCanonicalZorn v)
            (twistorCanonicalZorn w)) -
        canonicalVectorEquiv
          (InfoGeometry.Algebra.Zorn.CanonicalKantorOperators.V
            (twistorCanonicalZorn w) (twistorCanonicalZorn v)
            (twistorCanonicalZorn z)) := by
  rw [InfoGeometry.Algebra.Zorn.CanonicalKantorOperators.K,
    canonicalVectorEquiv_sub]
  rfl

/-- The native Kantor `K` action in its third argument, represented as a
linear operator on the complete canonical Zorn carrier. -/
noncomputable def canonicalKantorEnd
    (x y : CanonicalZorn) : Module.End ℝ CanonicalZorn where
  toFun z := InfoGeometry.Algebra.Zorn.CanonicalKantorOperators.K x y z
  map_add' := InfoGeometry.Algebra.Zorn.CanonicalKantorOperators.K_add_right x y
  map_smul' r z := InfoGeometry.Algebra.Zorn.CanonicalKantorOperators.K_smul_right r x y z

private theorem canonicalKantor_rootPair_positive_action (a c : Fin 3) :
    InfoGeometry.Algebra.Zorn.CanonicalKantorOperators.K
        (rootPlus a) (rootMinus a) (rootPlus c) = -rootPlus c := by
  rw [InfoGeometry.Algebra.Zorn.CanonicalKantorOperators.K_swap,
    InfoGeometry.Lie.SplitOctonionEllKantorRankOne.K_rootMinus_rootPlus_rootPlus_all]

/-- Every matched root-pair Kantor endomorphism preserves the axial grading.
The proof uses the computed action on both root sheets and both zero-weight
Peirce idempotents across all three root labels. -/
theorem canonicalKantor_rootPair_commutes_axialGrading (a : Fin 3) :
    canonicalKantorEnd
        (rootPlus a) (rootMinus a) *
      InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.axialGrading =
    InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.axialGrading *
      canonicalKantorEnd (rootPlus a) (rootMinus a) := by
  have hpos (c : Fin 3) := canonicalKantor_rootPair_positive_action a c
  have hneg (c : Fin 3) :=
    InfoGeometry.Lie.SplitOctonionEllKantorRankOne.K_rootPlus_rootMinus_rootMinus_all a c
  have huplus := InfoGeometry.Lie.SplitOctonionEllKantorRankOne.K_rootPlus_rootMinus_uPlus a
  have huminus := InfoGeometry.Lie.SplitOctonionEllKantorRankOne.K_rootPlus_rootMinus_uMinus a
  let D := canonicalKantorEnd (rootPlus a) (rootMinus a)
  have hD (i : Fin 8) : D
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis i) =
      if i.val < 4 then
        -(InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis i)
      else InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis i := by
    fin_cases i <;>
      simp [D, canonicalKantorEnd,
        InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis_apply,
        InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame,
        hpos, hneg, huplus, huminus]
  apply InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.ext
  intro i
  rw [Module.End.mul_apply, Module.End.mul_apply,
    InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.axialGrading_basis i,
    map_smul, hD i]
  fin_cases i <;> split_ifs <;>
    first
    | rw [map_neg,
        InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.axialGrading_basis]
    | rw [InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.axialGrading_basis]
  all_goals simp [InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.axialWeight]

/-- The matched-root Kantor action is itself tripotent on the full Zorn
carrier. Thus its adjoint action also has the general five-grade decomposition;
this is a second grading operator, built from the actual Kantor action. -/
theorem canonicalKantor_rootPair_tripotent (a : Fin 3) :
    let D := canonicalKantorEnd (rootPlus a) (rootMinus a)
    D * D * D = D := by
  have hpos (c : Fin 3) := canonicalKantor_rootPair_positive_action a c
  have hneg (c : Fin 3) :=
    InfoGeometry.Lie.SplitOctonionEllKantorRankOne.K_rootPlus_rootMinus_rootMinus_all a c
  have huplus := InfoGeometry.Lie.SplitOctonionEllKantorRankOne.K_rootPlus_rootMinus_uPlus a
  have huminus := InfoGeometry.Lie.SplitOctonionEllKantorRankOne.K_rootPlus_rootMinus_uMinus a
  let D := canonicalKantorEnd (rootPlus a) (rootMinus a)
  have hD (i : Fin 8) : D
      (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis i) =
      if i.val < 4 then
        -(InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis i)
      else InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis i := by
    fin_cases i <;>
      simp [D, canonicalKantorEnd,
        InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis_apply,
        InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame,
        hpos, hneg, huplus, huminus]
  apply InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis.ext
  intro i
  rw [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.circularPeirceBasis_apply]
  rw [Module.End.mul_apply, Module.End.mul_apply]
  by_cases hi : i.val < 4
  · have hEig : canonicalKantorEnd (rootPlus a) (rootMinus a)
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i) =
        -InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i := by
      simpa [D, hi] using hD i
    simpa only [hEig, map_neg, neg_neg]
  · have hEig : canonicalKantorEnd (rootPlus a) (rootMinus a)
        (InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i) =
        InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.frame i := by
      simpa [D, hi] using hD i
    simpa only [hEig]

/-- Each matched root-pair Kantor endomorphism lies in the actual zero-grade
projector range of the five-grading on the full endomorphism algebra. -/
theorem canonicalKantor_rootPair_mem_fiveGradeZero (a : Fin 3) :
    canonicalKantorEnd (rootPlus a) (rootMinus a) ∈
      InfoGeometry.Physics.Algebra.fiveGradeRange
        InfoGeometry.Lie.SplitOctonionPeirceFermionParityBridge.peirceDefectOperator
        .zero := by
  rw [InfoGeometry.Lie.SplitOctonionFiveGradeOperatorBridge.zornFiveGradeRange_eq_adjointEigenspace]
  rw [Module.End.mem_eigenspace_iff]
  simp only [InfoGeometry.Physics.Algebra.fiveGradeValue, Int.cast_zero, zero_smul]
  have hcomm := canonicalKantor_rootPair_commutes_axialGrading a
  change InfoGeometry.Lie.SplitOctonionPeirceFermionParityBridge.peirceDefectOperator *
      canonicalKantorEnd (rootPlus a) (rootMinus a) -
    canonicalKantorEnd (rootPlus a) (rootMinus a) *
      InfoGeometry.Lie.SplitOctonionPeirceFermionParityBridge.peirceDefectOperator = 0
  change InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.axialGrading *
      canonicalKantorEnd (rootPlus a) (rootMinus a) -
    canonicalKantorEnd (rootPlus a) (rootMinus a) *
      InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.axialGrading = 0
  rw [← hcomm]
  simp

attribute [local instance] LieRing.ofAssociativeRing

/-- The existing twistor-to-Zorn linear transport is onto the native
vector-matrix carrier. -/
theorem twistorZornLinearMap_surjective :
    Function.Surjective twistorZornLinearMap := by
  intro x
  refine ⟨twistorRealEquivZorn.symm (canonicalVectorEquiv.symm x), ?_⟩
  change canonicalVectorEquiv
    (twistorRealEquivZorn (twistorRealEquivZorn.symm (canonicalVectorEquiv.symm x))) = x
  rw [LinearEquiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The twistor operator lift has exactly the native left-multiplication
range, because the twistor-to-Zorn carrier map is onto. -/
theorem twistorOperatorLift_range_eq_leftMultiplication_range :
    LinearMap.range twistorOperatorLift = LinearMap.range leftMultiplication := by
  ext T
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨twistorZornLinearMap z, ?_⟩
    change leftMultiplication (twistorZornLinearMap z) = T at hz
    exact hz
  · rintro ⟨X, hX⟩
    obtain ⟨z, hz⟩ := twistorZornLinearMap_surjective X
    refine ⟨z, ?_⟩
    calc
      twistorOperatorLift z = leftMultiplication X := by
        change leftMultiplication (twistorZornLinearMap z) = _
        rw [hz]
      _ = T := hX

/-- The pointwise images of the two equal ranges agree as sets. -/
theorem twistorOperatorLift_set_range_eq_leftMultiplication :
    Set.range twistorOperatorLift = Set.range leftMultiplication := by
  ext T
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨twistorZornLinearMap z, rfl⟩
  · rintro ⟨X, hX⟩
    obtain ⟨z, hz⟩ := twistorZornLinearMap_surjective X
    refine ⟨z, ?_⟩
    calc
      twistorOperatorLift z = leftMultiplication X := by
        change leftMultiplication (twistorZornLinearMap z) = _
        rw [hz]
      _ = T := hX

/-- The associator defect of two lifted twistors belongs to the Lie algebra
generated by the twistor operator image. -/
theorem twistorOperatorLift_product_defect_mem_lieSpan (z w : Twistor4) :
    twistorOperatorLift (twistorMul z w) -
        twistorOperatorLift z * twistorOperatorLift w ∈
      LieSubalgebra.lieSpan ℝ
        (Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ))
        (Set.range twistorOperatorLift) := by
  rw [twistorOperatorLift_product_defect]
  rw [twistorOperatorLift_set_range_eq_leftMultiplication]
  exact multiplicationDefect_mem_native_lieSpan
    (twistorZornLinearMap z) (twistorZornLinearMap w)

/-- The explicit nonzero associator defect from the twistor preimages of
`U 0` and `U 1` is a new Lie-closure direction, outside the linear range of
the twistor operator lift. -/
theorem twistorOperatorLift_U01_defect_not_mem_range :
    twistorOperatorLift (twistorMul (twistorPreimageU 0) (twistorPreimageU 1)) -
        twistorOperatorLift (twistorPreimageU 0) *
          twistorOperatorLift (twistorPreimageU 1) ∉ LinearMap.range twistorOperatorLift := by
  rw [twistorOperatorLift_product_defect,
    twistorOperatorLift_range_eq_leftMultiplication_range]
  exact nonzero_multiplicationDefect_not_mem_left_range
    (twistorZornLinearMap (twistorPreimageU 0))
    (twistorZornLinearMap (twistorPreimageU 1))
    (by simpa [twistorPreimageU, twistorZornLinearMap,
      canonicalZornToVectorLinearMap, LinearMap.comp_apply] using
        multiplicationDefect_U01_ne_zero)

/-- The Lie closure of the faithful twistor operator image strictly exceeds
that image itself. -/
theorem twistorOperatorLift_range_lt_lieSpan :
    LinearMap.range twistorOperatorLift <
      (LieSubalgebra.lieSpan ℝ
        (Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ))
        (Set.range twistorOperatorLift)).toSubmodule := by
  rw [twistorOperatorLift_range_eq_leftMultiplication_range,
    twistorOperatorLift_set_range_eq_leftMultiplication]
  exact left_action_range_lt_native_lieSpan

/-- Transport the native axial tripotent to the vector-matrix carrier used by
the associative algebra of lifted operators. -/
noncomputable def axialTripotentOnVectorMatrices :
    Module.End ℝ (InfoGeometry.Algebra.ZornVectorMatrix ℝ) :=
  canonicalVectorLinearEquiv.toLinearMap.comp
    (axialGrading.comp canonicalVectorLinearEquiv.symm.toLinearMap)

/-- The transported axial operator remains tripotent on the operator-lift
carrier. -/
theorem axialTripotentOnVectorMatrices_tripotent :
    axialTripotentOnVectorMatrices * axialTripotentOnVectorMatrices *
        axialTripotentOnVectorMatrices = axialTripotentOnVectorMatrices := by
  apply LinearMap.ext
  intro x
  change canonicalVectorLinearEquiv
      (axialGrading (axialGrading (axialGrading (canonicalVectorLinearEquiv.symm x)))) =
    canonicalVectorLinearEquiv (axialGrading (canonicalVectorLinearEquiv.symm x))
  exact congrArg canonicalVectorLinearEquiv
    (congrArg (fun f : Module.End ℝ
      InfoGeometry.Lie.SplitOctonionEllCircularAxialGrading.CanonicalZorn =>
        f (canonicalVectorLinearEquiv.symm x))
      axialGrading_tripotent)

/-- The explicit nonassociative Zorn associator is not fixed by the zero-grade
projector of the transported axial tripotent. Its commutator with that
tripotent is therefore nonzero. -/
theorem U01_associator_defect_axial_commutator_on_rootPlus_two :
    (axialTripotentOnVectorMatrices *
        multiplicationDefect (canonicalVectorEquiv (rootPlus 0))
          (canonicalVectorEquiv (rootPlus 1)) -
      multiplicationDefect (canonicalVectorEquiv (rootPlus 0))
        (canonicalVectorEquiv (rootPlus 1)) * axialTripotentOnVectorMatrices)
        (canonicalVectorEquiv (rootPlus 2)) =
      -canonicalVectorEquiv (uMinus - uPlus) := by
  have huPlus : axialGrading uPlus = 0 := by
    change (1 / 2 : ℝ) • ellCommutator uPlus = 0
    rw [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.ellCommutator_uPlus]
    simp only [smul_zero]
  have huMinus : axialGrading uMinus = 0 := by
    change (1 / 2 : ℝ) • ellCommutator uMinus = 0
    rw [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.ellCommutator_uMinus]
    simp only [smul_zero]
  have hroot2 : axialGrading (rootPlus 2) = rootPlus 2 := by
    change (1 / 2 : ℝ) • ellCommutator (rootPlus 2) = rootPlus 2
    rw [ellCommutator_rootPlus]
    norm_num [smul_smul]
  have hassoc := rootPlus_associator_zero_one_two
  have hdefect : multiplicationDefect
      (canonicalVectorEquiv (rootPlus 0)) (canonicalVectorEquiv (rootPlus 1))
      (canonicalVectorEquiv (rootPlus 2)) =
        canonicalVectorEquiv (uMinus - uPlus) := by
    change InfoGeometry.Algebra.ZornVectorMatrix.associator
      (canonicalVectorEquiv (rootPlus 0)) (canonicalVectorEquiv (rootPlus 1))
      (canonicalVectorEquiv (rootPlus 2)) = _
    calc
      _ = canonicalVectorEquiv
          ((rootPlus 0 * rootPlus 1) * rootPlus 2 -
            rootPlus 0 * (rootPlus 1 * rootPlus 2)) := by
          simp only [InfoGeometry.Algebra.ZornVectorMatrix.associator,
            canonicalVectorEquiv_sub, canonicalVectorEquiv_mul]
      _ = canonicalVectorEquiv (uMinus - uPlus) := by rw [hassoc]
  have hfirst : canonicalVectorLinearEquiv (axialGrading
      (canonicalVectorLinearEquiv.symm
        (multiplicationDefect (canonicalVectorEquiv (rootPlus 0))
          (canonicalVectorEquiv (rootPlus 1)) (canonicalVectorEquiv (rootPlus 2))))) = 0 := by
    rw [hdefect]
    change canonicalVectorLinearEquiv
      (axialGrading (canonicalVectorLinearEquiv.symm
        (canonicalVectorLinearEquiv (uMinus - uPlus)))) = 0
    rw [canonicalVectorLinearEquiv.symm_apply_apply, map_sub, huMinus, huPlus]
    simp only [sub_self]
    exact canonicalVectorLinearEquiv.map_zero
  have hsecond : multiplicationDefect (canonicalVectorEquiv (rootPlus 0))
      (canonicalVectorEquiv (rootPlus 1))
      (canonicalVectorLinearEquiv (axialGrading
        (canonicalVectorLinearEquiv.symm (canonicalVectorEquiv (rootPlus 2))))) =
      canonicalVectorEquiv (uMinus - uPlus) := by
    change multiplicationDefect (canonicalVectorEquiv (rootPlus 0))
      (canonicalVectorEquiv (rootPlus 1))
      (canonicalVectorLinearEquiv (axialGrading
        (canonicalVectorLinearEquiv.symm (canonicalVectorLinearEquiv (rootPlus 2))))) =
      canonicalVectorLinearEquiv (uMinus - uPlus)
    rw [canonicalVectorLinearEquiv.symm_apply_apply, hroot2]
    exact hdefect
  change canonicalVectorLinearEquiv (axialGrading (canonicalVectorLinearEquiv.symm
      (multiplicationDefect (canonicalVectorEquiv (rootPlus 0))
        (canonicalVectorEquiv (rootPlus 1)) (canonicalVectorEquiv (rootPlus 2))))) -
    multiplicationDefect (canonicalVectorEquiv (rootPlus 0))
      (canonicalVectorEquiv (rootPlus 1))
      (canonicalVectorLinearEquiv (axialGrading
        (canonicalVectorLinearEquiv.symm (canonicalVectorEquiv (rootPlus 2))))) =
    -canonicalVectorEquiv (uMinus - uPlus)
  rw [hfirst, hsecond]
  rw [zero_sub]

/-- The explicit associator defect does not commute with the transported
axial tripotent. -/
theorem U01_associator_defect_axial_commutator_ne_zero :
    axialTripotentOnVectorMatrices *
        multiplicationDefect (canonicalVectorEquiv (rootPlus 0))
          (canonicalVectorEquiv (rootPlus 1)) -
      multiplicationDefect (canonicalVectorEquiv (rootPlus 0))
        (canonicalVectorEquiv (rootPlus 1)) * axialTripotentOnVectorMatrices ≠ 0 := by
  intro h
  have heval := LinearMap.congr_fun h (canonicalVectorEquiv (rootPlus 2))
  change (axialTripotentOnVectorMatrices *
      multiplicationDefect (canonicalVectorEquiv (rootPlus 0))
        (canonicalVectorEquiv (rootPlus 1)) -
    multiplicationDefect (canonicalVectorEquiv (rootPlus 0))
      (canonicalVectorEquiv (rootPlus 1)) * axialTripotentOnVectorMatrices)
      (canonicalVectorEquiv (rootPlus 2)) = 0 at heval
  rw [U01_associator_defect_axial_commutator_on_rootPlus_two] at heval
  have hsep : canonicalVectorEquiv (uMinus - uPlus) ≠ 0 := by
    intro hz
    have hdiff : uMinus - uPlus = 0 := by
      apply canonicalVectorEquiv.injective
      exact hz
    have haxis : uPlus - uMinus = 0 := by
      calc
        uPlus - uMinus = -(uMinus - uPlus) := by abel
        _ = 0 := by rw [hdiff]; simp
    have hl : InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit ≠ 0 := by
      intro h
      have hx := congrArg
        (fun X : InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.CanonicalZorn => X.x 0) h
      norm_num [InfoGeometry.Algebra.Zorn.SplitQuaternionCore.lUnit] at hx
    rw [uPlus_sub_uMinus] at haxis
    exact hl haxis
  have hzero : canonicalVectorEquiv (uMinus - uPlus) = 0 := by
    exact (neg_eq_zero.mp heval)
  exact hsep hzero

/-- The concrete `U₀₁` associator has a nonzero grade `-1` component:
the grade projector, evaluated on the `+1` root vector, returns the
associator value. This identifies the grade, rather than merely asserting
that some nonzero grade occurs. -/
theorem U01_associator_defect_negOne_grade_component_on_rootPlus_two :
    InfoGeometry.Physics.Algebra.fiveGradeProjector
        axialTripotentOnVectorMatrices .negOne
        (multiplicationDefect (canonicalVectorEquiv (rootPlus 0))
          (canonicalVectorEquiv (rootPlus 1)))
        (canonicalVectorEquiv (rootPlus 2)) =
      canonicalVectorEquiv (uMinus - uPlus) := by
  let t := axialTripotentOnVectorMatrices
  let defect := multiplicationDefect (canonicalVectorEquiv (rootPlus 0))
    (canonicalVectorEquiv (rootPlus 1))
  let x := canonicalVectorEquiv (rootPlus 2)
  let y := canonicalVectorEquiv (uMinus - uPlus)
  have ht : t * t * t = t := axialTripotentOnVectorMatrices_tripotent
  have huPlus : axialGrading uPlus = 0 := by
    change (1 / 2 : ℝ) • ellCommutator uPlus = 0
    rw [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.ellCommutator_uPlus]
    simp only [smul_zero]
  have huMinus : axialGrading uMinus = 0 := by
    change (1 / 2 : ℝ) • ellCommutator uMinus = 0
    rw [InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis.ellCommutator_uMinus]
    simp only [smul_zero]
  have hroot : axialGrading (rootPlus 2) = rootPlus 2 := by
    change (1 / 2 : ℝ) • ellCommutator (rootPlus 2) = rootPlus 2
    rw [ellCommutator_rootPlus]
    norm_num [smul_smul]
  have hx : t x = x := by
    change canonicalVectorLinearEquiv
      (axialGrading (canonicalVectorLinearEquiv.symm x)) = x
    change canonicalVectorLinearEquiv
      (axialGrading (canonicalVectorLinearEquiv.symm
        (canonicalVectorLinearEquiv (rootPlus 2)))) =
      canonicalVectorLinearEquiv (rootPlus 2)
    rw [canonicalVectorLinearEquiv.symm_apply_apply]
    exact congrArg canonicalVectorLinearEquiv hroot
  have hy : t y = 0 := by
    change canonicalVectorLinearEquiv
      (axialGrading (canonicalVectorLinearEquiv.symm y)) = 0
    change canonicalVectorLinearEquiv
      (axialGrading (canonicalVectorLinearEquiv.symm
        (canonicalVectorLinearEquiv (uMinus - uPlus)))) = 0
    rw [canonicalVectorLinearEquiv.symm_apply_apply, map_sub,
      huMinus, huPlus]
    simp only [sub_self, map_zero]
  have hdefect : defect x = y := by
    change multiplicationDefect (canonicalVectorEquiv (rootPlus 0))
      (canonicalVectorEquiv (rootPlus 1)) (canonicalVectorEquiv (rootPlus 2)) = _
    change InfoGeometry.Algebra.ZornVectorMatrix.associator
      (canonicalVectorEquiv (rootPlus 0)) (canonicalVectorEquiv (rootPlus 1))
      (canonicalVectorEquiv (rootPlus 2)) = _
    calc
      _ = canonicalVectorEquiv
          ((rootPlus 0 * rootPlus 1) * rootPlus 2 -
            rootPlus 0 * (rootPlus 1 * rootPlus 2)) := by
          simp only [InfoGeometry.Algebra.ZornVectorMatrix.associator,
            canonicalVectorEquiv_sub, canonicalVectorEquiv_mul]
      _ = y := by rw [rootPlus_associator_zero_one_two]
  have hPosX : InfoGeometry.Physics.Algebra.peirceProjector t .pos x = x := by
    change (1 / 2 : ℝ) • (t (t x) + t x) = x
    rw [hx, hx]
    rw [← two_smul ℝ x, smul_smul]
    norm_num
  have hZeroX : InfoGeometry.Physics.Algebra.peirceProjector t .zero x = 0 := by
    change x - t (t x) = 0
    rw [hx, hx]
    simp
  have hZeroY : InfoGeometry.Physics.Algebra.peirceProjector t .zero y = y := by
    change y - t (t y) = y
    rw [hy, map_zero]
    simp
  have hNegOneEval :
      InfoGeometry.Physics.Algebra.gradeNegOneProjector t defect x = y := by
    unfold InfoGeometry.Physics.Algebra.gradeNegOneProjector
      InfoGeometry.Physics.Algebra.jointPeirceProjector
      InfoGeometry.Physics.Algebra.peirceLeft
      InfoGeometry.Physics.Algebra.peirceRight
      InfoGeometry.Physics.Algebra.leftMulLinear
      InfoGeometry.Physics.Algebra.rightMulLinear
    change InfoGeometry.Physics.Algebra.peirceProjector t .zero
        (defect (InfoGeometry.Physics.Algebra.peirceProjector t .pos x)) +
      InfoGeometry.Physics.Algebra.peirceProjector t .neg
        (defect (InfoGeometry.Physics.Algebra.peirceProjector t .zero x)) = y
    rw [hPosX, hZeroX]
    simp only [map_zero]
    rw [hdefect, hZeroY]
    simp
  simpa [t, defect, x, y, InfoGeometry.Physics.Algebra.fiveGradeProjector] using
    hNegOneEval

/-- The actual U₀₁ associator anomaly has a nonzero component in one of the
four nonzero axial five-grades of the full operator algebra. -/
theorem U01_associator_defect_has_nonzero_five_grade :
    ∃ k : InfoGeometry.Physics.Algebra.FiveGrade, k ≠ .zero ∧
      InfoGeometry.Physics.Algebra.fiveGradeProjector axialTripotentOnVectorMatrices k
        (multiplicationDefect (canonicalVectorEquiv (rootPlus 0))
          (canonicalVectorEquiv (rootPlus 1))) ≠ 0 := by
  apply InfoGeometry.Core.TripotentAdjoint.exists_nonzero_nonzero_grade_component_of_ad_ne_zero
    axialTripotentOnVectorMatrices_tripotent
  exact U01_associator_defect_axial_commutator_ne_zero

/-- A twistor is in the radical of the infinity form exactly when its
faithful operator lift is the lift of its first-spinor sheet. -/
theorem infinity_radical_iff_operator_lift_is_first_sheet (z : Twistor4) :
    infinityTwistor z = 0 ↔
      twistorOperatorLift z = twistorOperatorLift (plusInclusion z.1) := by
  constructor
  · intro hz
    have hSecond : z.2 = 0 := (infinityTwistor_radical z).mp hz
    apply congrArg twistorOperatorLift
    apply Prod.ext
    · rfl
    · exact hSecond
  · intro hLift
    have hz : z = plusInclusion z.1 := twistorOperatorLift_injective hLift
    apply (infinityTwistor_radical z).mpr
    have hSecond := congrArg Prod.snd hz
    simpa [plusInclusion] using hSecond

/-- The Plücker `p23` incidence condition against every twistor is exactly
the condition that the faithful operator lift has no second-sheet part. This
identifies the Klein-Plücker radical with the first-sheet operator carrier. -/
theorem plucker_p23_radical_iff_operator_lift_is_first_sheet (z : Twistor4) :
    (∀ w : Twistor4,
      (InfoGeometry.Twistor.TwoTwistorPlucker.twistorPairPlucker z w).p23 = 0) ↔
      twistorOperatorLift z = twistorOperatorLift (plusInclusion z.1) := by
  constructor
  · intro hp
    apply (infinity_radical_iff_operator_lift_is_first_sheet z).mp
    apply LinearMap.ext
    intro w
    rw [InfoGeometry.Twistor.InfinityTwistor.infinityTwistor_eq_plucker_p23]
    exact hp w
  · intro hLift w
    have hRad : infinityTwistor z = 0 :=
      (infinity_radical_iff_operator_lift_is_first_sheet z).mpr hLift
    rw [← InfoGeometry.Twistor.InfinityTwistor.infinityTwistor_eq_plucker_p23]
    have hEval := congrArg (fun f : Module.Dual ℂ Twistor4 => f w) hRad
    simpa using hEval

/-- On the infinity radical, the twistor operator is precisely the
left-regular Zorn action of the first chiral sheet. -/
theorem infinity_radical_operator_lift_eq_first_sheet_action
    (z : Twistor4) (hz : infinityTwistor z = 0) :
    twistorOperatorLift z =
      leftMultiplication (canonicalVectorEquiv (plusZornMap z.1)) := by
  rw [twistorOperatorLift_chiral_decomposition]
  have hSecond : z.2 = 0 := (infinityTwistor_radical z).mp hz
  rw [hSecond]
  rw [map_zero minusZornMap, canonicalVectorEquiv_zero]
  change leftMultiplication (canonicalVectorEquiv (plusZornMap z.1)) +
      leftMultiplication (0 : InfoGeometry.Algebra.ZornPinorReconstruction.Z) = _
  rw [map_zero leftMultiplication, add_zero]

end InfoGeometry.Twistor.InfinityTwistorOperatorLiftBridge

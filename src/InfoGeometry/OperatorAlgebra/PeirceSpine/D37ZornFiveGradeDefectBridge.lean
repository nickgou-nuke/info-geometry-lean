/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeItFromBitLogisticPoset
import InfoGeometry.OperatorAlgebra.NCZornDefectFiveGradeSupport

/-!
# D₃₇ idempotency anomaly in the native Zorn five-grade decomposition

Specialize the associative operator ring in D₃₇ to endomorphisms of the
noncommutative operator-Zorn carrier. The logistic variance remains its own
idempotency anomaly; this bridge decomposes that anomaly into the existing
five Peirce charge grades. It does not identify it with the distinct
nonassociative multiplication-composition defect.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.D37ZornFiveGradeDefectBridge

open InfoGeometry.OperatorAlgebra.NCZornTripotentFiveGrading
open InfoGeometry.OperatorAlgebra.NCZornDefectFiveGradeSupport
open InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeItFromBitLogisticPoset
open InfoGeometry.OperatorAlgebra.PeirceSpine.NonCommutativeOperatorTimePoset
open InfoGeometry.Canonical.OperatorZornRealModule
open InfoGeometry.Canonical
open InfoGeometry.Physics.NCG

variable {A : Type*} [Ring A]

/-- The five-grade projection is additive-negation compatible. -/
theorem ncZornFiveComponent_neg (K : Module.End ℤ (OperatorZornMatrix A)) (d : Fin 5) :
    ncZornFiveComponent (-K) d = -ncZornFiveComponent K d := by
  fin_cases d <;> simp [ncZornFiveComponent, ncZornBlock] <;> abel

/-- The five-grade projections are additive, so defect identities transport
componentwise without losing any of the anomaly grades. -/
theorem ncZornFiveComponent_add
    (K L : Module.End ℤ (OperatorZornMatrix A)) (d : Fin 5) :
    ncZornFiveComponent (K + L) d =
      ncZornFiveComponent K d + ncZornFiveComponent L d := by
  fin_cases d <;> simp [ncZornFiveComponent, ncZornBlock_add] <;> abel

/-- Each five-grade projection is integer-linear. -/
theorem ncZornFiveComponent_zsmul
    (n : ℤ) (K : Module.End ℤ (OperatorZornMatrix A)) (d : Fin 5) :
    ncZornFiveComponent (n • K) d = n • ncZornFiveComponent K d := by
  have hcentral (x : Module.End ℤ (OperatorZornMatrix A)) :
      (n : ℤ) * x = x * (n : ℤ) := Int.cast_commute n x
  fin_cases d <;>
    simp [ncZornFiveComponent, ncZornBlock, mul_assoc, hcentral]

/-- The D₃₇ corner-flux counter transports grade by grade: each native Zorn
charge component records `k` times the corresponding component of the bulk
operator. -/
theorem bitCounterOp_five_grade_channel_count
    {P U W : Module.End ℤ (OperatorZornMatrix A)} (hP : P * P = P)
    (k : ℤ) (d : Fin 5) :
    ncZornFiveComponent
        (bitCounterOp P W (unipotentCornerOp k P U)
          (unipotentCornerOpInv k P U)) d =
      k • ncZornFiveComponent (genV P U W) d := by
  have hCount :
      bitCounterOp P W (unipotentCornerOp k P U)
        (unipotentCornerOpInv k P U) = k • genV P U W :=
    (multi_channel_bit_counting_and_additivity (P := P)
      (V₁ := (0 : Module.End ℤ (OperatorZornMatrix A))) (V₂ := 0)
      hP (zero_mul (0 : Module.End ℤ (OperatorZornMatrix A)))
      (mul_zero (0 : Module.End ℤ (OperatorZornMatrix A))) U W k).2
  rw [hCount, ncZornFiveComponent_zsmul]

/-- Every native five-grade projection sends the zero endomorphism to zero. -/
theorem ncZornFiveComponent_zero (d : Fin 5) :
    ncZornFiveComponent (0 : Module.End ℤ (OperatorZornMatrix A)) d = 0 := by
  fin_cases d <;> simp [ncZornFiveComponent, ncZornBlock]

/-- In the endomorphism operator ring, the D₃₇ logistic variance is the
negative idempotency defect of its bulk generator. -/
theorem logisticBitVariance_eq_neg_bulk_idempotency_defect
    {P U W : Module.End ℤ (OperatorZornMatrix A)} (hP : P * P = P) :
    logisticBitVariance P U W = -idemDefect (genV P U W) := by
  exact (logistic_bit_variance_and_defect_equivalence hP U W).2.2.2

/-- Each D₃₇ logistic-anomaly grade is the negative of the corresponding
grade of the bulk idempotency defect. -/
theorem logisticBitVariance_five_grade_component
    {P U W : Module.End ℤ (OperatorZornMatrix A)} (hP : P * P = P)
    (d : Fin 5) :
    ncZornFiveComponent (logisticBitVariance P U W) d =
      -ncZornFiveComponent (idemDefect (genV P U W)) d := by
  rw [logisticBitVariance_eq_neg_bulk_idempotency_defect hP]
  exact ncZornFiveComponent_neg _ d

/-- Reversing the two commuting logistic factors leaves every native Zorn
charge grade unchanged. In particular, the reverse-ordered variance carries
the same five graded defect contributions as the forward-ordered variance. -/
theorem logisticBitVariance_reverse_order_five_grade_component
    {P U W : Module.End ℤ (OperatorZornMatrix A)} (hP : P * P = P)
    (d : Fin 5) :
    ncZornFiveComponent
        (logisticBitMinus P U W * logisticBitPlus P U W) d =
      ncZornFiveComponent (logisticBitVariance P U W) d ∧
    ncZornFiveComponent
        (logisticBitMinus P U W * logisticBitPlus P U W) d =
      -ncZornFiveComponent (idemDefect (genV P U W)) d := by
  have hOrder := logistic_bit_variance_order_independence hP U W
  constructor
  · exact congrArg (fun K : Module.End ℤ (OperatorZornMatrix A) =>
      ncZornFiveComponent K d) hOrder.2.2.symm
  · rw [hOrder.1]
    exact ncZornFiveComponent_neg _ d

/-- Each graded logistic anomaly is an exact integer-charge eigenoperator of
the native Zorn tripotent. The five-grade decomposition therefore retains the
charge of the idempotency defect at every grade. -/
theorem logisticBitVariance_five_grade_charge
    {P U W : Module.End ℤ (OperatorZornMatrix A)} (hP : P * P = P)
    (d : Fin 5) :
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (ncZornTripotent (A := A))
        (ncZornFiveComponent (logisticBitVariance P U W) d) =
      ((d.val : ℤ) - 2) •
        ncZornFiveComponent (logisticBitVariance P U W) d := by
  have hDefectCharge :=
    ncZornFiveComponent_comm_tripotent (idemDefect (genV P U W)) d
  rw [logisticBitVariance_eq_neg_bulk_idempotency_defect hP,
    ncZornFiveComponent_neg]
  have hCommNeg (X : Module.End ℤ (OperatorZornMatrix A)) :
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm (ncZornTripotent (A := A)) (-X) =
        -InfoGeometry.OperatorAlgebra.PeirceSpine.comm (ncZornTripotent (A := A)) X := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    noncomm_ring
  rw [hCommNeg, hDefectCharge]
  rw [smul_neg]

/-- The plus logistic bit's idempotency anomaly is the bulk defect in each
of the five Zorn charge grades. -/
theorem logisticBitPlus_defect_five_grade_component
    {P U W : Module.End ℤ (OperatorZornMatrix A)} (hP : P * P = P)
    (d : Fin 5) :
    ncZornFiveComponent (idemDefect (logisticBitPlus P U W)) d =
      ncZornFiveComponent (idemDefect (genV P U W)) d := by
  have hDef := (logistic_bit_variance_and_defect_equivalence hP U W).2.1
  exact congrArg (fun K : Module.End ℤ (OperatorZornMatrix A) =>
    ncZornFiveComponent K d) hDef

/-- The minus logistic bit carries the same idempotency anomaly in each of
the five Zorn charge grades. -/
theorem logisticBitMinus_defect_five_grade_component
    {P U W : Module.End ℤ (OperatorZornMatrix A)} (hP : P * P = P)
    (d : Fin 5) :
    ncZornFiveComponent (idemDefect (logisticBitMinus P U W)) d =
      ncZornFiveComponent (idemDefect (genV P U W)) d := by
  have hDef := (logistic_bit_variance_and_defect_equivalence hP U W).2.2.1
  exact congrArg (fun K : Module.End ℤ (OperatorZornMatrix A) =>
    ncZornFiveComponent K d) hDef

/-- Orthogonal-channel idempotency-defect additivity holds separately in
each of the five Zorn charge grades. This transports the core D₃₇ channel
identity instead of collapsing the anomaly to its total sum. -/
theorem orthogonal_channel_defect_five_grade_additivity
    {V₁ V₂ : Module.End ℤ (OperatorZornMatrix A)}
    (h12 : V₁ * V₂ = 0) (h21 : V₂ * V₁ = 0)
    (d : Fin 5) :
    ncZornFiveComponent (idemDefect (V₁ + V₂)) d =
      ncZornFiveComponent (idemDefect V₁) d +
        ncZornFiveComponent (idemDefect V₂) d := by
  have hAdd :=
    orthogonal_idempotency_defect_additivity h12 h21
  calc
    ncZornFiveComponent
        (NonCommutativeOperatorTimePoset.idemDefect (V₁ + V₂)) d =
        ncZornFiveComponent
          (NonCommutativeOperatorTimePoset.idemDefect V₁ +
            NonCommutativeOperatorTimePoset.idemDefect V₂) d := by rw [hAdd]
    _ = ncZornFiveComponent (NonCommutativeOperatorTimePoset.idemDefect V₁) d +
        ncZornFiveComponent (NonCommutativeOperatorTimePoset.idemDefect V₂) d :=
      ncZornFiveComponent_add _ _ d

/-- Finite-family orthogonal defect additivity is retained in every native
five-grade component. Thus each charge grade records the sum of the channel
defects independently. -/
theorem orthogonal_channel_defect_sum_five_grade_additivity
    {ι : Type*} (s : Finset ι)
    (f : ι → Module.End ℤ (OperatorZornMatrix A))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      f i * f j = 0 ∧ f j * f i = 0)
    (d : Fin 5) :
    ncZornFiveComponent (NonCommutativeOperatorTimePoset.idemDefect
      (∑ i ∈ s, f i)) d =
      ∑ i ∈ s, ncZornFiveComponent
        (NonCommutativeOperatorTimePoset.idemDefect (f i)) d := by
  classical
  have hDefect := orthogonal_idempotency_defect_sum s f horth
  have hComponentSum (t : Finset ι) :
      ncZornFiveComponent
          (∑ i ∈ t, NonCommutativeOperatorTimePoset.idemDefect (f i)) d =
        ∑ i ∈ t,
          ncZornFiveComponent
            (NonCommutativeOperatorTimePoset.idemDefect (f i)) d := by
    induction t using Finset.induction_on with
    | empty => exact ncZornFiveComponent_zero d
    | @insert a t ha ih =>
        simp only [Finset.sum_insert ha, ncZornFiveComponent_add]
        rw [ih]
  rw [hDefect]
  exact hComponentSum s

/-- The five readouts in the D₃₇ full-circle identity agree grade by grade,
not only after summing their five Peirce components. -/
theorem five_way_full_circle_five_grade_component
    {P U W : Module.End ℤ (OperatorZornMatrix A)} (hP : P * P = P)
    (d : Fin 5) :
    ncZornFiveComponent (-logisticBitVariance P U W) d =
        ncZornFiveComponent (idemDefect (genV P U W)) d ∧
    ncZornFiveComponent (idemDefect (logisticBitPlus P U W)) d =
        ncZornFiveComponent (idemDefect (genV P U W)) d ∧
    ncZornFiveComponent (-(cohomologyProj P U W * genV P U W)) d =
        ncZornFiveComponent (idemDefect (genV P U W)) d ∧
    ncZornFiveComponent (zornNorm P (genV P U W + genPhi P U W)) d =
        ncZornFiveComponent (idemDefect (genV P U W)) d ∧
    ncZornFiveComponent
        (idemDefectBar (genPhi P U W) * idemDefect (genPhi P U W)) d =
      ncZornFiveComponent (idemDefect (genV P U W)) d := by
  rcases five_way_full_circle_unification_identity hP U W with
    ⟨h1, h2, h3, h4, h5⟩
  exact ⟨congrArg (fun K : Module.End ℤ (OperatorZornMatrix A) =>
      ncZornFiveComponent K d) h1,
    congrArg (fun K : Module.End ℤ (OperatorZornMatrix A) =>
      ncZornFiveComponent K d) h2,
    congrArg (fun K : Module.End ℤ (OperatorZornMatrix A) =>
      ncZornFiveComponent K d) h3,
    congrArg (fun K : Module.End ℤ (OperatorZornMatrix A) =>
      ncZornFiveComponent K d) h4,
    congrArg (fun K : Module.End ℤ (OperatorZornMatrix A) =>
      ncZornFiveComponent K d) h5⟩

/-- The full D₃₇ logistic variance is the sum of its five operator-Zorn
charge components, with each component retaining its defect contribution. -/
theorem logisticBitVariance_five_grade_expansion
    {P U W : Module.End ℤ (OperatorZornMatrix A)} :
    logisticBitVariance P U W =
      ∑ d : Fin 5, ncZornFiveComponent (logisticBitVariance P U W) d := by
  exact (ncZornFiveComponent_sum (logisticBitVariance P U W)).symm

/-- A nonzero D₃₇ logistic anomaly is detected in at least one of its five
operator-Zorn charge grades. -/
theorem logisticBitVariance_nonzero_has_five_grade_support
    {P U W : Module.End ℤ (OperatorZornMatrix A)}
    (hVar : logisticBitVariance P U W ≠ 0) :
    ∃ d : Fin 5, ncZornFiveComponent (logisticBitVariance P U W) d ≠ 0 := by
  exact exists_nonzero_five_grade_component _ hVar

/-- D₃₇ crystallization is equivalent to vanishing of every native
five-grade component of the bulk idempotency defect. This records the full
anomaly criterion: no grade is discarded when passing between the global
variance and its graded readouts. -/
theorem logisticBitVariance_zero_iff_all_five_defect_grades_zero
    {P U W : Module.End ℤ (OperatorZornMatrix A)} (hP : P * P = P) :
    logisticBitVariance P U W = 0 ↔
      ∀ d : Fin 5, ncZornFiveComponent (idemDefect (genV P U W)) d = 0 := by
  constructor
  · intro hVar d
    have hDefect : idemDefect (genV P U W) = 0 :=
      (bit_crystallization_iff_zero_logistic_variance hP U W).2.mp hVar
    rw [hDefect]
    exact ncZornFiveComponent_zero d
  · intro hGrades
    have hSum :
        ∑ d : Fin 5, ncZornFiveComponent (idemDefect (genV P U W)) d = 0 :=
      Finset.sum_eq_zero fun d _ => hGrades d
    have hDefect : idemDefect (genV P U W) = 0 := by
      rw [ncZornFiveComponent_sum] at hSum
      exact hSum
    rw [logisticBitVariance_eq_neg_bulk_idempotency_defect hP, hDefect]
    simp

/-- Crystallization is controlled grade by grade by the full idempotency
anomaly: the logistic plus operator is idempotent exactly when each of the
five native Zorn-grade components of the bulk defect vanishes. This exposes
the anomaly grades as the complete generators of the on-shell criterion. -/
theorem logisticBit_crystallization_iff_all_five_anomaly_grades_vanish
    {P U W : Module.End ℤ (OperatorZornMatrix A)} (hP : P * P = P) :
    (logisticBitPlus P U W * logisticBitPlus P U W = logisticBitPlus P U W) ↔
      ∀ d : Fin 5,
        ncZornFiveComponent (idemDefect (genV P U W)) d = 0 := by
  constructor
  · intro hIdem
    have hVariance : logisticBitVariance P U W = 0 :=
      (logistic_bit_crystallization_full_equivalence hP U W).1.mp hIdem
    exact (logisticBitVariance_zero_iff_all_five_defect_grades_zero hP).mp
      hVariance
  · intro hGrades
    have hVariance : logisticBitVariance P U W = 0 :=
      (logisticBitVariance_zero_iff_all_five_defect_grades_zero hP).mpr
        hGrades
    exact (logistic_bit_crystallization_full_equivalence hP U W).1.mpr
      hVariance

/-- The graded D₃₇ master readout keeps the complete logistic anomaly visible:
the variance is the negative bulk idempotency defect, its five components
sum back to the variance, each component retains its Zorn charge, and
crystallization occurs exactly when every defect grade vanishes. -/
theorem stage_D37_five_grade_defect_master_readout
    {P U W : Module.End ℤ (OperatorZornMatrix A)} (hP : P * P = P) :
    logisticBitVariance P U W = -idemDefect (genV P U W) ∧
    logisticBitVariance P U W =
      ∑ d : Fin 5, ncZornFiveComponent (logisticBitVariance P U W) d ∧
    (∀ d : Fin 5,
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm
        (ncZornTripotent (A := A))
        (ncZornFiveComponent (logisticBitVariance P U W) d) =
        ((d.val : ℤ) - 2) •
          ncZornFiveComponent (logisticBitVariance P U W) d) ∧
    ((logisticBitPlus P U W * logisticBitPlus P U W = logisticBitPlus P U W) ↔
      ∀ d : Fin 5,
        ncZornFiveComponent (idemDefect (genV P U W)) d = 0) := by
  refine ⟨logisticBitVariance_eq_neg_bulk_idempotency_defect hP, ?_, ?_,
    logisticBit_crystallization_iff_all_five_anomaly_grades_vanish hP⟩
  · exact logisticBitVariance_five_grade_expansion
  · intro d
    exact logisticBitVariance_five_grade_charge hP d

end InfoGeometry.OperatorAlgebra.PeirceSpine.D37ZornFiveGradeDefectBridge

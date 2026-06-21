import InfoGeometry.SuperMetriplectic.SupertraceBodyBridge
import InfoGeometry.Clifford.Grading

/-!
# Involution-Adapted Chiral Doubled Basis

Conservative formal program for rewriting the scalar super-metriplectic shadow
in the basis suggested by the operator geometry:

* chiral left/right scalar channels;
* doubled real total/exchange channels;
* regular/defect and compact/noncompact involution eigenspaces;
* reversible/dissipative metriplectic lanes.

The module is deliberately a basis-adaptation layer.  It does not assert that a
global operator lift exists.  Instead it exposes the blockwise obligations that
an operator lift should satisfy once the scalar shadow has been split along the
involutions.
-/

namespace InfoGeometry.SuperMetriplectic

/--
Scalar chiral/doubled basis.

`left` and `right` are the primitive chiral scalar channels.  The doubled real
coordinates are represented by their total and exchange combinations.
-/
structure ChiralDoubledScalarBasis where
  left : ℝ
  right : ℝ
  total : ℝ
  exchange : ℝ
  total_eq_left_add_right : total = left + right
  exchange_eq_left_sub_right : exchange = left - right

namespace ChiralDoubledScalarBasis

/-- The doubled total channel is the sum of the chiral channels. -/
theorem total_eq (B : ChiralDoubledScalarBasis) :
    B.total = B.left + B.right :=
  B.total_eq_left_add_right

/-- The doubled exchange channel is the left-minus-right chiral channel. -/
theorem exchange_eq (B : ChiralDoubledScalarBasis) :
    B.exchange = B.left - B.right :=
  B.exchange_eq_left_sub_right

/-- Left/right equality is equivalent to vanishing doubled exchange. -/
theorem exchange_eq_zero_iff_left_eq_right
    (B : ChiralDoubledScalarBasis) :
    B.exchange = 0 ↔ B.left = B.right := by
  rw [B.exchange_eq]
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    rw [h]
    simp

end ChiralDoubledScalarBasis

/--
Scalar involution-adapted split.

Each pair is a plus/minus decomposition for one organizing involution:

* regular/defect: Penrose/Drazin separation;
* compact/noncompact: Cartan split;
* reversible/dissipative: metriplectic split.
-/
structure InvolutionAdaptedScalarSplit where
  regular : ℝ
  defect : ℝ
  compact : ℝ
  noncompact : ℝ
  reversible : ℝ
  dissipative : ℝ
  regularDefectTotal : ℝ
  cartanTotal : ℝ
  flowTotal : ℝ
  regularDefectTotal_eq : regularDefectTotal = regular + defect
  cartanTotal_eq : cartanTotal = compact + noncompact
  flowTotal_eq : flowTotal = reversible + dissipative

namespace InvolutionAdaptedScalarSplit

/-- The Drazin/Penrose shadow splits into regular and defect channels. -/
theorem regularDefectTotal_eq_add
    (S : InvolutionAdaptedScalarSplit) :
    S.regularDefectTotal = S.regular + S.defect :=
  S.regularDefectTotal_eq

/-- The Cartan shadow splits into compact and noncompact channels. -/
theorem cartanTotal_eq_add
    (S : InvolutionAdaptedScalarSplit) :
    S.cartanTotal = S.compact + S.noncompact :=
  S.cartanTotal_eq

/-- The metriplectic shadow splits into reversible and dissipative channels. -/
theorem flowTotal_eq_add
    (S : InvolutionAdaptedScalarSplit) :
    S.flowTotal = S.reversible + S.dissipative :=
  S.flowTotal_eq

/-- If the defect coordinate vanishes, the regular/defect total is regular. -/
theorem regularDefectTotal_eq_regular_of_defect_zero
    (S : InvolutionAdaptedScalarSplit)
    (h : S.defect = 0) :
    S.regularDefectTotal = S.regular := by
  rw [S.regularDefectTotal_eq, h]
  simp

/-- If the dissipative coordinate vanishes, the flow total is reversible. -/
theorem flowTotal_eq_reversible_of_dissipative_zero
    (S : InvolutionAdaptedScalarSplit)
    (h : S.dissipative = 0) :
    S.flowTotal = S.reversible := by
  rw [S.flowTotal_eq, h]
  simp

end InvolutionAdaptedScalarSplit

/--
Adapted scalar packet for the super-metriplectic layer.

This joins the chiral/doubled coordinates, involution eigenspace coordinates,
Schur/Drazin hidden block, and body/supertrace entropy shadow.  The important
point is that the global scalar shadow is reconstructed from localized blocks.
-/
structure InvolutionAdaptedSuperMetriplecticBasis where
  chiral : ChiralDoubledScalarBasis
  split : InvolutionAdaptedScalarSplit
  schur : ScalarSchurDrazinBlock
  fisher : SupertraceFisherShadow
  globalShadow : ℝ
  globalShadow_eq_localized_blocks :
    globalShadow =
      chiral.total
        + split.regularDefectTotal
        + split.cartanTotal
        + split.flowTotal
        + schur.effectiveEvenOnsager
        + fisher.bodyFisherQuadratic

namespace InvolutionAdaptedSuperMetriplecticBasis

/--
In an adapted basis the global scalar shadow is a sum of localized blocks,
rather than one opaque mixed expression.
-/
theorem globalShadow_eq_blocks
    (B : InvolutionAdaptedSuperMetriplecticBasis) :
    B.globalShadow =
      B.chiral.total
        + B.split.regularDefectTotal
        + B.split.cartanTotal
        + B.split.flowTotal
        + B.schur.effectiveEvenOnsager
        + B.fisher.bodyFisherQuadratic :=
  B.globalShadow_eq_localized_blocks

/-- The Schur block remains the Moore-Penrose-stabilized hidden elimination. -/
theorem schur_block_eq
    (B : InvolutionAdaptedSuperMetriplecticBasis) :
    B.schur.effectiveEvenOnsager =
      B.schur.LPP - B.schur.LPΘ * B.schur.penrose.aPlus * B.schur.LΘP :=
  B.schur.effectiveEvenOnsager_eq

/-- The Drazin defect lane remains isolated as its own projector shadow. -/
theorem drazin_defect_projector_eq
    (B : InvolutionAdaptedSuperMetriplecticBasis) :
    B.schur.drazinDefectProjector =
      1 - B.schur.LΘΘ * B.schur.drazin.aD :=
  B.schur.drazinDefectProjector_eq

/-- Body Fisher positivity survives the adapted-basis rewrite. -/
theorem body_fisher_nonnegative
    (B : InvolutionAdaptedSuperMetriplecticBasis) :
    0 ≤ B.fisher.bodyFisherQuadratic :=
  B.fisher.body_second

/-- The raw supertrace readout remains signed in the adapted basis. -/
theorem supertrace_signed
    (B : InvolutionAdaptedSuperMetriplecticBasis) :
    B.fisher.supertraceQuadratic =
      B.fisher.evenQuadratic
        - B.fisher.oddQuadratic
        + B.fisher.nilpotentCancellation :=
  B.fisher.supertrace_eq

/--
Capstone for the scalar adapted-basis layer:
localized reconstruction, Schur elimination, Drazin defect isolation, body
positivity, and signed supertrace are simultaneously exposed.
-/
theorem adapted_basis_capstone
    (B : InvolutionAdaptedSuperMetriplecticBasis) :
    B.globalShadow =
        B.chiral.total
          + B.split.regularDefectTotal
          + B.split.cartanTotal
          + B.split.flowTotal
          + B.schur.effectiveEvenOnsager
          + B.fisher.bodyFisherQuadratic
      ∧ B.schur.effectiveEvenOnsager =
          B.schur.LPP - B.schur.LPΘ * B.schur.penrose.aPlus * B.schur.LΘP
      ∧ B.schur.drazinDefectProjector =
          1 - B.schur.LΘΘ * B.schur.drazin.aD
      ∧ 0 ≤ B.fisher.bodyFisherQuadratic
      ∧ B.fisher.supertraceQuadratic =
          B.fisher.evenQuadratic
            - B.fisher.oddQuadratic
            + B.fisher.nilpotentCancellation := by
  exact ⟨B.globalShadow_eq_blocks,
    B.schur_block_eq,
    B.drazin_defect_projector_eq,
    B.body_fisher_nonnegative,
    B.supertrace_signed⟩

end InvolutionAdaptedSuperMetriplecticBasis

/--
Blockwise operator-lift obligation packet.

The point is architectural: after scalar basis adaptation, the global lift is
represented as a conjunction of smaller lane-wise obligations rather than a
single unsplit theorem.
-/
structure BlockwiseOperatorLiftObligations where
  leftLift : Prop
  rightLift : Prop
  exchangeLift : Prop
  defectLift : Prop
  cartanLift : Prop
  flowLift : Prop
  leftLift_proof : leftLift
  rightLift_proof : rightLift
  exchangeLift_proof : exchangeLift
  defectLift_proof : defectLift
  cartanLift_proof : cartanLift
  flowLift_proof : flowLift

namespace BlockwiseOperatorLiftObligations

/-- The global operator lift obligation is the product of the lane-wise lifts. -/
theorem global_lift
    (O : BlockwiseOperatorLiftObligations) :
    O.leftLift
      ∧ O.rightLift
      ∧ O.exchangeLift
      ∧ O.defectLift
      ∧ O.cartanLift
      ∧ O.flowLift :=
  ⟨O.leftLift_proof,
    O.rightLift_proof,
    O.exchangeLift_proof,
    O.defectLift_proof,
    O.cartanLift_proof,
    O.flowLift_proof⟩

end BlockwiseOperatorLiftObligations

/-! ## Repo-native doubled chiral projector bridge -/

namespace DoubledChiralProjectorBridge

open InfoGeometry.Krein

section Doubled

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E

/-- The doubled real carrier has a canonical chiral projector sum. -/
theorem grade_projectors_sum :
    gradePlusProj (E := E) + gradeMinusProj (E := E) =
      ContinuousLinearMap.id ℝ H₂ :=
  gradeProj_sum (E := E)

/-- The plus/minus chiral projectors annihilate in one order. -/
theorem grade_plus_comp_minus_zero :
    (gradePlusProj (E := E)).comp (gradeMinusProj (E := E)) = 0 :=
  gradePlusProj_comp_gradeMinusProj (E := E)

/-- The minus/plus chiral projectors annihilate in the opposite order. -/
theorem grade_minus_comp_plus_zero :
    (gradeMinusProj (E := E)).comp (gradePlusProj (E := E)) = 0 :=
  gradeMinusProj_comp_gradePlusProj (E := E)

end Doubled

end DoubledChiralProjectorBridge

end InfoGeometry.SuperMetriplectic

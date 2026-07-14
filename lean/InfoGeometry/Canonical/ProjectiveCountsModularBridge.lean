import InfoGeometry.Canonical.RelativePotentialCountBridge
import InfoGeometry.Meta.Architecture

open scoped BigOperators InnerProductSpace

noncomputable section

namespace ProjectiveCountsModularBridge

open InfoGeometry.Canonical.RelativePotentialCountBridge
open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Krein

/-!
# Projective counts / modular bridge

This file packages the finite count origin of the modular scalar/operator lane.

The owner count-side API already lives in `RelativePotentialCountBridge`.  This
module adds a small theorem-facing readback:

* positive count profiles determine projective count rays;
* common positive rescaling does not change the count ray;
* common nonzero rescaling does not change the raw relative ratio;
* therefore the averaged modular scalar and its scalar/Krein operator lifts are
  invariant under common rescaling.

No density matrix, trace, complex scalar, or analytic modular flow is introduced
here.
-/

section CountRays

variable {n : Nat} [Nonempty (Fin n)]

/-- Positive common rescaling of a count profile. -/
@[rep_depth projective]
def positiveRescaleCounts
    (c : ℝ)
    (counts : RelativeCounts n) : RelativeCounts n :=
  c • counts

/-- Positive rescaling preserves strict positivity of a count profile. -/
@[rep_depth projective]
theorem positiveRescaleCounts_pos
    (c : ℝ)
    (hc : 0 < c)
    (counts : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i) :
    ∀ i : Fin n, 0 < positiveRescaleCounts (n := n) c counts i := by
  intro i
  unfold positiveRescaleCounts
  exact mul_pos hc (hcounts i)

/--
Projective count ray associated to a positive finite count profile.

This is an alias for the owner `countRay`, used to make the bridge statement
read in count-language.
-/
@[rep_depth projective]
noncomputable def projectiveCountRay
    (counts : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i) :
    PositiveRay (Fin n) :=
  countRay counts hcounts

/-- Common positive rescaling does not change the projective count ray. -/
@[rep_depth projective]
theorem projectiveCountRay_positiveRescale
    (c : ℝ)
    (hc : 0 < c)
    (counts : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i) :
    projectiveCountRay
        (positiveRescaleCounts (n := n) c counts)
        (positiveRescaleCounts_pos (n := n) c hc counts hcounts)
      =
    projectiveCountRay counts hcounts := by
  unfold projectiveCountRay countRay
  let μ := positiveMeasureOfCounts counts hcounts
  let ν := positiveMeasureOfCounts
    (positiveRescaleCounts (n := n) c counts)
    (positiveRescaleCounts_pos (n := n) c hc counts hcounts)
  have hsame : InfoGeometry.PositiveMeasure.SameRay μ ν := by
    refine ⟨(⟨c, hc⟩ : InfoGeometry.Stratum.PosGauge), ?_⟩
    ext i
    change InfoGeometry.PositiveMeasure.scale c hc (positiveMeasureOfCounts counts hcounts) i = c * counts i
    rfl
  exact (Quotient.sound hsame).symm

/-- The canonical gauge section is also invariant under common positive rescaling. -/
@[rep_depth projective]
theorem gaugeSection_projectiveCountRay_positiveRescale
    (c : ℝ)
    (hc : 0 < c)
    (counts : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i) :
    gaugeSection (α := Fin n)
        (projectiveCountRay
          (positiveRescaleCounts (n := n) c counts)
          (positiveRescaleCounts_pos (n := n) c hc counts hcounts))
      =
    gaugeSection (α := Fin n) (projectiveCountRay counts hcounts) := by
  rw [projectiveCountRay_positiveRescale (n := n) c hc counts hcounts]

end CountRays

/-! ## Relative count ratio and modular scalar readbacks -/

section RelativeRatio

variable (n : Nat)

/-- Count-side relative ratio. Alias for the owner raw count `Δ`. -/
@[rep_depth projective]
noncomputable def relativeCountRatio
    (counts ref : RelativeCounts n) : Fin n → ℝ :=
  rawCountDelta n counts ref

/-- Common nonzero rescaling does not change the relative count ratio. -/
@[rep_depth projective]
theorem relativeCountRatio_common_smul
    (c : ℝ)
    (hc : c ≠ 0)
    (counts ref : RelativeCounts n) :
    relativeCountRatio n (c • counts) (c • ref)
      =
    relativeCountRatio n counts ref := by
  simpa [relativeCountRatio] using
    rawCountDelta_common_smul (n := n) c hc counts ref

/-- Modular scalar obtained from the count-side relative ratio. -/
@[rep_depth projective]
noncomputable def countModularScalar
    (counts ref : RelativeCounts n) : ℝ :=
  averagedRawCountHamiltonian n counts ref

/-- Common nonzero rescaling does not change the count modular scalar. -/
@[rep_depth projective]
theorem countModularScalar_common_smul
    (c : ℝ)
    (hc : c ≠ 0)
    (counts ref : RelativeCounts n) :
    countModularScalar n (c • counts) (c • ref)
      =
    countModularScalar n counts ref := by
  simpa [countModularScalar] using
    averagedRawCountHamiltonian_common_smul (n := n) c hc counts ref

end RelativeRatio

/-! ## Scalar and Krein-native operator lifts -/

section OperatorLift

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lift a real modular scalar to the isotropic scalar operator. -/
@[rep_depth operator]
noncomputable def scalarOperatorLift (a : ℝ) : E →L[ℝ] E :=
  a • ContinuousLinearMap.id ℝ E

@[rep_depth operator, simp]
theorem scalarOperatorLift_apply
    (a : ℝ)
    (x : E) :
    scalarOperatorLift (E := E) a x = a • x := by
  simp [scalarOperatorLift]

@[rep_depth operator, simp]
theorem scalarOperatorLift_common_smul_readback
    (n : Nat)
    (c : ℝ)
    (hc : c ≠ 0)
    (counts ref : RelativeCounts n) :
    scalarOperatorLift (E := E)
        (countModularScalar n (c • counts) (c • ref))
      =
    scalarOperatorLift (E := E) (countModularScalar n counts ref) := by
  rw [countModularScalar_common_smul (n := n) c hc counts ref]

end OperatorLift

section CountOperatorLift

variable (n : Nat)

/-- Isotropic doubled operator lift of the count modular scalar. -/
@[rep_depth projective]
noncomputable def countScalarOperatorLift
    (counts ref : RelativeCounts n) :
    AlgebraEnd (RouterAmplitude n) :=
  averagedRawCountTomitaTakesakiOp n counts ref

/-- Krein-native doubled operator lift of the count modular scalar. -/
@[rep_depth projective]
noncomputable def countKreinOperatorLift
    (counts ref : RelativeCounts n) :
    AlgebraEnd (RouterAmplitude n) :=
  averagedRawCountKreinTomitaTakesakiOp n counts ref

@[rep_depth projective, simp]
theorem countScalarOperatorLift_apply
    (counts ref : RelativeCounts n)
    (v : DoubledSpace (RouterAmplitude n)) :
    countScalarOperatorLift n counts ref v =
      countModularScalar n counts ref • v := by
  simp [countScalarOperatorLift, countModularScalar]

@[rep_depth projective, simp]
theorem countKreinOperatorLift_apply
    (counts ref : RelativeCounts n)
    (v : DoubledSpace (RouterAmplitude n)) :
    countKreinOperatorLift n counts ref v =
      countModularScalar n counts ref •
        (InfoGeometry.Krein.spectral_epsilon (E := RouterAmplitude n) v) := by
  simp [countKreinOperatorLift, countModularScalar]

/-- Common nonzero rescaling does not change the isotropic count operator lift. -/
@[rep_depth projective]
theorem countScalarOperatorLift_common_smul
    (c : ℝ)
    (hc : c ≠ 0)
    (counts ref : RelativeCounts n) :
    countScalarOperatorLift n (c • counts) (c • ref)
      =
    countScalarOperatorLift n counts ref := by
  simpa [countScalarOperatorLift] using
    averagedRawCountTomitaTakesakiOp_common_smul (n := n) c hc counts ref

/-- Common nonzero rescaling does not change the Krein-native count operator lift. -/
@[rep_depth projective]
theorem countKreinOperatorLift_common_smul
    (c : ℝ)
    (hc : c ≠ 0)
    (counts ref : RelativeCounts n) :
    countKreinOperatorLift n (c • counts) (c • ref)
      =
    countKreinOperatorLift n counts ref := by
  simpa [countKreinOperatorLift] using
    averagedRawCountKreinTomitaTakesakiOp_common_smul (n := n) c hc counts ref

end CountOperatorLift

end ProjectiveCountsModularBridge

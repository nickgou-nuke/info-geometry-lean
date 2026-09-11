import InfoGeometry.Canonical.RealBdG
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RestrictedSheetContinuous

namespace InfoGeometry.Canonical.RealBdGSheetBridge

open InfoGeometry.Canonical.MongeAmpereDualSheetBridge
open InfoGeometry.Canonical.RestrictedSheetContinuous
open InfoGeometry.Krein

section Basic

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Swap the plus and minus sheet automorphisms. -/
def swapSheets (g : RestrictedSheetContinuousEquiv E) : RestrictedSheetContinuousEquiv E where
  plus := g.minus
  minus := g.plus

/-- Common-mode average of the two sheet actions. -/
noncomputable def commonModeMap (g : RestrictedSheetContinuousEquiv E) : E →L[ℝ] E :=
  (1 / 2 : ℝ) •
    (g.plus.toContinuousLinearMap + g.minus.toContinuousLinearMap)

/-- Chiral imbalance half-difference of the two sheet actions. -/
noncomputable def chiralImbalanceMap (g : RestrictedSheetContinuousEquiv E) : E →L[ℝ] E :=
  (1 / 2 : ℝ) •
    (g.plus.toContinuousLinearMap - g.minus.toContinuousLinearMap)

/-- Diagonal common-mode lift determined by the RealBdG `K`-linear sector. -/
noncomputable abbrev commonModeLift (g : RestrictedSheetContinuousEquiv E) : EndH :=
  dualSheetLift (E := E) (commonModeMap (E := E) g)

/-- Chiral lift determined by the RealBdG `K`-antilinear sector. -/
noncomputable def dualSheetChiralLift (A : E →L[ℝ] E) : EndH :=
  (plusPointL (E := E)).comp (A.comp (fst_L (E := E))) -
    (minusPointL (E := E)).comp (A.comp (snd_L (E := E)))

/-- Chiral lift of the sheet imbalance. -/
noncomputable abbrev chiralImbalanceLift (g : RestrictedSheetContinuousEquiv E) : EndH :=
  dualSheetChiralLift (E := E) (chiralImbalanceMap (E := E) g)

omit [CompleteSpace E] in
@[simp] theorem dualSheetChiralLift_apply_to_doubled
    (A : E →L[ℝ] E) (x xi : E) :
    dualSheetChiralLift (E := E) A (to_doubled x xi : H₂) = to_doubled (A x) (-A xi) := by
  apply DoubledSpace.ext
  · simp [dualSheetChiralLift, plusPointL, minusPointL, to_doubled]
  · simp [dualSheetChiralLift, plusPointL, minusPointL, to_doubled]

omit [CompleteSpace E] in
@[simp] theorem plusBlockMap_dualSheetChiralLift
    (A : E →L[ℝ] E) :
    plusBlockMap (E := E) (dualSheetChiralLift (E := E) A) = A := by
  ext x
  simp [plusBlockMap, dualSheetChiralLift]

omit [CompleteSpace E] in
@[simp] theorem minusBlockMap_dualSheetChiralLift
    (A : E →L[ℝ] E) :
    minusBlockMap (E := E) (dualSheetChiralLift (E := E) A) = -A := by
  ext x
  simp [minusBlockMap, dualSheetChiralLift]

omit [CompleteSpace E] in
@[simp] theorem plusToMinusBlockMap_dualSheetChiralLift
    (A : E →L[ℝ] E) :
    plusToMinusBlockMap (E := E) (dualSheetChiralLift (E := E) A) = 0 := by
  ext x
  simp [plusToMinusBlockMap, dualSheetChiralLift]

omit [CompleteSpace E] in
@[simp] theorem minusToPlusBlockMap_dualSheetChiralLift
    (A : E →L[ℝ] E) :
    minusToPlusBlockMap (E := E) (dualSheetChiralLift (E := E) A) = 0 := by
  ext x
  simp [minusToPlusBlockMap, dualSheetChiralLift]

@[simp] theorem KConjugate_liftedOperator
    (g : RestrictedSheetContinuousEquiv E) :
    InfoGeometry.Canonical.RealBdG.KConjugate (E := E)
        (RestrictedSheetContinuousEquiv.liftedOperator (E := E) g)
      = -(RestrictedSheetContinuousEquiv.liftedOperator (E := E) (swapSheets g)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : u = to_doubled (WithLp.fst u) (WithLp.snd u) := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [hu]
  apply DoubledSpace.ext
  · simp [InfoGeometry.Canonical.RealBdG.KConjugate, InfoGeometry.Canonical.RealBdG.modularK,
      swapSheets, RestrictedSheetContinuousEquiv.liftedOperator_apply_to_doubled,
      ContinuousLinearMap.comp_apply]
  · simp [InfoGeometry.Canonical.RealBdG.KConjugate, InfoGeometry.Canonical.RealBdG.modularK,
      swapSheets, RestrictedSheetContinuousEquiv.liftedOperator_apply_to_doubled,
      ContinuousLinearMap.comp_apply]

@[simp] theorem KLinearPart_liftedOperator
    (g : RestrictedSheetContinuousEquiv E) :
    InfoGeometry.Canonical.RealBdG.KLinearPart (E := E)
        (RestrictedSheetContinuousEquiv.liftedOperator (E := E) g)
      = commonModeLift (E := E) g := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : u = to_doubled (WithLp.fst u) (WithLp.snd u) := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [hu]
  apply DoubledSpace.ext
  · simp [InfoGeometry.Canonical.RealBdG.KLinearPart, commonModeLift, commonModeMap,
      KConjugate_liftedOperator, RestrictedSheetContinuousEquiv.liftedOperator_apply_to_doubled,
      dualSheetLift_apply_to_doubled, swapSheets, sub_eq_add_neg]
  · simp [InfoGeometry.Canonical.RealBdG.KLinearPart, commonModeLift, commonModeMap,
      KConjugate_liftedOperator, RestrictedSheetContinuousEquiv.liftedOperator_apply_to_doubled,
      dualSheetLift_apply_to_doubled, swapSheets, sub_eq_add_neg]
    abel

@[simp] theorem KAntilinearPart_liftedOperator
    (g : RestrictedSheetContinuousEquiv E) :
    InfoGeometry.Canonical.RealBdG.KAntilinearPart (E := E)
        (RestrictedSheetContinuousEquiv.liftedOperator (E := E) g)
      = chiralImbalanceLift (E := E) g := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : u = to_doubled (WithLp.fst u) (WithLp.snd u) := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [hu]
  apply DoubledSpace.ext
  · simp [InfoGeometry.Canonical.RealBdG.KAntilinearPart, chiralImbalanceLift, chiralImbalanceMap,
      KConjugate_liftedOperator, RestrictedSheetContinuousEquiv.liftedOperator_apply_to_doubled,
      dualSheetChiralLift_apply_to_doubled, swapSheets, sub_eq_add_neg]
  · simp [InfoGeometry.Canonical.RealBdG.KAntilinearPart, chiralImbalanceLift, chiralImbalanceMap,
      KConjugate_liftedOperator, RestrictedSheetContinuousEquiv.liftedOperator_apply_to_doubled,
      dualSheetChiralLift_apply_to_doubled, swapSheets, sub_eq_add_neg]

 theorem commonModeLift_is_KLinear
    (g : RestrictedSheetContinuousEquiv E) :
    InfoGeometry.Canonical.RealBdG.KLinear (E := E) (commonModeLift (E := E) g) := by
  simpa [KLinearPart_liftedOperator] using
    (InfoGeometry.Canonical.RealBdG.kSplit_linear (E := E)
      (A := RestrictedSheetContinuousEquiv.liftedOperator (E := E) g))

theorem chiralImbalanceLift_is_KAntilinear
    (g : RestrictedSheetContinuousEquiv E) :
    InfoGeometry.Canonical.RealBdG.KAntilinear (E := E) (chiralImbalanceLift (E := E) g) := by
  simpa [KAntilinearPart_liftedOperator] using
    (InfoGeometry.Canonical.RealBdG.kSplit_antilinear (E := E)
      (A := RestrictedSheetContinuousEquiv.liftedOperator (E := E) g))

@[simp] theorem KAntilinearPart_liftedOperator_eq_zero_of_isGaugeBalanced
    {g : RestrictedSheetContinuousEquiv E}
    (hg : RestrictedSheetContinuousEquiv.IsGaugeBalanced (E := E) g) :
    InfoGeometry.Canonical.RealBdG.KAntilinearPart (E := E)
        (RestrictedSheetContinuousEquiv.liftedOperator (E := E) g) = 0 := by
  have hchi : chiralImbalanceMap (E := E) g = 0 := by
    ext x
    have hx : g.plus x = g.minus x := by
      simpa using congrArg (fun f : E ≃L[ℝ] E => f x) hg
    simp [chiralImbalanceMap, hx]
  rw [KAntilinearPart_liftedOperator]
  rw [chiralImbalanceLift, hchi]
  ext u <;> simp [dualSheetChiralLift, plusPointL, minusPointL]

@[simp] theorem KLinearPart_liftedOperator_eq_liftedOperator_of_isGaugeBalanced
    {g : RestrictedSheetContinuousEquiv E}
    (hg : RestrictedSheetContinuousEquiv.IsGaugeBalanced (E := E) g) :
    InfoGeometry.Canonical.RealBdG.KLinearPart (E := E)
        (RestrictedSheetContinuousEquiv.liftedOperator (E := E) g)
      = RestrictedSheetContinuousEquiv.liftedOperator (E := E) g := by
  have hcommon : commonModeMap (E := E) g = g.plus.toContinuousLinearMap := by
    ext x
    have hx : g.plus x = g.minus x := by
      simpa using congrArg (fun f : E ≃L[ℝ] E => f x) hg
    simp [commonModeMap, hx]
    module
  simpa [commonModeLift, hcommon] using
    (RestrictedSheetContinuousEquiv.liftedOperator_eq_dualSheetLift_of_isGaugeBalanced
      (E := E) hg).symm

end Basic

end InfoGeometry.Canonical.RealBdGSheetBridge

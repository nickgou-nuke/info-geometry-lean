import InfoGeometry.Canonical.BogoliubovProjectorFlux
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.MongeAmpereCramerRao
import InfoGeometry.Canonical.CalabiYauRNMongeAmpere
import InfoGeometry.Krein.PolarizedSector

namespace InfoGeometry.Canonical.MongeAmpereDualSheetBridge

open InfoGeometry.Convex
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.MongeAmpereCramerRao
open InfoGeometry.Canonical.CalabiYauBridge
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Canonical.BogoliubovClosedForms
open InfoGeometry.Canonical.BogoliubovProjectorTransport
open InfoGeometry.Canonical.BogoliubovProjectorFlux
open InfoGeometry.Canonical.SpectralInference
open InfoGeometry.Canonical.MoE
open InfoGeometry.Krein
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Krein.PolarizedSector

section Lift

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- Positive-sheet embedding as a continuous linear map. -/
noncomputable def plusPointL : E →L[ℝ] H₂ where
  toFun x := plusPoint (E := E) x
  map_add' x y := by
    apply DoubledSpace.ext <;> simp [plusPoint, to_doubled]
  map_smul' c x := by
    apply DoubledSpace.ext <;> simp [plusPoint, to_doubled]
  cont := by
    simpa [plusPoint, to_doubled] using
      (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := E) (β := E)).comp
        ((continuous_id : Continuous fun x : E => x).prodMk
          (continuous_const : Continuous fun _ : E => (0 : E)))

/-- Negative-sheet embedding as a continuous linear map. -/
noncomputable def minusPointL : E →L[ℝ] H₂ where
  toFun x := minusPoint (E := E) x
  map_add' x y := by
    apply DoubledSpace.ext <;> simp [minusPoint, to_doubled]
  map_smul' c x := by
    apply DoubledSpace.ext <;> simp [minusPoint, to_doubled]
  cont := by
    simpa [minusPoint, to_doubled] using
      (WithLp.prod_continuous_toLp (p := (2 : ENNReal)) (α := E) (β := E)).comp
        ((continuous_const : Continuous fun _ : E => (0 : E)).prodMk
          (continuous_id : Continuous fun x : E => x))

omit [CompleteSpace E] in
@[simp] theorem plusPointL_apply (x : E) :
    plusPointL (E := E) x = plusPoint (E := E) x := rfl

omit [CompleteSpace E] in
@[simp] theorem minusPointL_apply (x : E) :
    minusPointL (E := E) x = minusPoint (E := E) x := rfl

/-- Diagonal lift of an `E`-operator to the doubled carrier. -/
noncomputable def dualSheetLift (A : E →L[ℝ] E) : EndH :=
  (plusPointL (E := E)).comp (A.comp (fst_L (E := E))) +
    (minusPointL (E := E)).comp (A.comp (snd_L (E := E)))

omit [CompleteSpace E] in
@[simp] theorem dualSheetLift_apply_to_doubled
    (A : E →L[ℝ] E) (x ξ : E) :
    dualSheetLift (E := E) A (to_doubled x ξ : H₂) = to_doubled (A x) (A ξ) := by
  apply DoubledSpace.ext <;>
    simp [dualSheetLift, plusPointL, minusPointL, plusPoint, minusPoint, to_doubled,
      ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem dualSheetLift_apply_plusPoint
    (A : E →L[ℝ] E) (x : E) :
    dualSheetLift (E := E) A (plusPoint (E := E) x) = plusPoint (E := E) (A x) := by
  apply DoubledSpace.ext <;>
    simp [dualSheetLift, plusPointL, minusPointL, plusPoint, minusPoint, to_doubled,
      ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem dualSheetLift_apply_minusPoint
    (A : E →L[ℝ] E) (ξ : E) :
    dualSheetLift (E := E) A (minusPoint (E := E) ξ) = minusPoint (E := E) (A ξ) := by
  apply DoubledSpace.ext <;>
    simp [dualSheetLift, plusPointL, minusPointL, plusPoint, minusPoint, to_doubled,
      ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem fst_dualSheetLift
    (A : E →L[ℝ] E) (u : H₂) :
    WithLp.fst (dualSheetLift (E := E) A u) = A (WithLp.fst u) := by
  simp [dualSheetLift, plusPointL, minusPointL, plusPoint, minusPoint, to_doubled,
    ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem snd_dualSheetLift
    (A : E →L[ℝ] E) (u : H₂) :
    WithLp.snd (dualSheetLift (E := E) A u) = A (WithLp.snd u) := by
  simp [dualSheetLift, plusPointL, minusPointL, plusPoint, minusPoint, to_doubled,
    ContinuousLinearMap.comp_apply]

theorem plusPointL_eq_adjoint_fstL :
    plusPointL (E := E) = ContinuousLinearMap.adjoint (fst_L (E := E)) := by
  refine (ContinuousLinearMap.eq_adjoint_iff
    (A := plusPointL (E := E))
    (B := fst_L (E := E))).2 ?_
  intro x y
  simp [plusPointL, plusPoint, to_doubled]

@[simp] theorem plusPointL_adjoint :
    ContinuousLinearMap.adjoint (plusPointL (E := E)) = fst_L (E := E) := by
  have h := congrArg ContinuousLinearMap.adjoint (plusPointL_eq_adjoint_fstL (E := E))
  simpa [ContinuousLinearMap.adjoint_adjoint] using h

@[simp] theorem fst_L_adjoint :
    ContinuousLinearMap.adjoint (fst_L (E := E)) = plusPointL (E := E) := by
  simp [plusPointL_eq_adjoint_fstL (E := E)]

theorem minusPointL_eq_adjoint_sndL :
    minusPointL (E := E) = ContinuousLinearMap.adjoint (snd_L (E := E)) := by
  refine (ContinuousLinearMap.eq_adjoint_iff
    (A := minusPointL (E := E))
    (B := snd_L (E := E))).2 ?_
  intro x y
  simp [minusPointL, minusPoint, to_doubled]

@[simp] theorem minusPointL_adjoint :
    ContinuousLinearMap.adjoint (minusPointL (E := E)) = snd_L (E := E) := by
  have h := congrArg ContinuousLinearMap.adjoint (minusPointL_eq_adjoint_sndL (E := E))
  simpa [ContinuousLinearMap.adjoint_adjoint] using h

@[simp] theorem snd_L_adjoint :
    ContinuousLinearMap.adjoint (snd_L (E := E)) = minusPointL (E := E) := by
  simp [minusPointL_eq_adjoint_sndL (E := E)]

@[simp] theorem dualSheetLift_star (A : E →L[ℝ] E) :
    star (dualSheetLift (E := E) A) = dualSheetLift (E := E) (star A) := by
  unfold dualSheetLift
  simp [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc]

omit [CompleteSpace E] in
@[simp] theorem dualSheetLift_neg (A : E →L[ℝ] E) :
    dualSheetLift (E := E) (-A) = -dualSheetLift (E := E) A := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [dualSheetLift, plusPointL, minusPointL, ContinuousLinearMap.comp_apply]

/-- Positive-to-positive block extracted on the base carrier `E`. -/
noncomputable def plusBlockMap (T : EndH) : E →L[ℝ] E :=
  (fst_L (E := E)).comp (T.comp (plusPointL (E := E)))

/-- Negative-to-negative block extracted on the base carrier `E`. -/
noncomputable def minusBlockMap (T : EndH) : E →L[ℝ] E :=
  (snd_L (E := E)).comp (T.comp (minusPointL (E := E)))

/-- Positive-to-negative block extracted on the base carrier `E`. -/
noncomputable def plusToMinusBlockMap (T : EndH) : E →L[ℝ] E :=
  (snd_L (E := E)).comp (T.comp (plusPointL (E := E)))

/-- Negative-to-positive block extracted on the base carrier `E`. -/
noncomputable def minusToPlusBlockMap (T : EndH) : E →L[ℝ] E :=
  (fst_L (E := E)).comp (T.comp (minusPointL (E := E)))

omit [CompleteSpace E] in
@[simp] theorem plusBlockMap_dualSheetLift
    (A : E →L[ℝ] E) :
    plusBlockMap (E := E) (dualSheetLift (E := E) A) = A := by
  ext x
  simp [plusBlockMap]

omit [CompleteSpace E] in
@[simp] theorem minusBlockMap_dualSheetLift
    (A : E →L[ℝ] E) :
    minusBlockMap (E := E) (dualSheetLift (E := E) A) = A := by
  ext x
  simp [minusBlockMap]

omit [CompleteSpace E] in
@[simp] theorem plusToMinusBlockMap_dualSheetLift
    (A : E →L[ℝ] E) :
    plusToMinusBlockMap (E := E) (dualSheetLift (E := E) A) = 0 := by
  ext x
  simp [plusToMinusBlockMap]

omit [CompleteSpace E] in
@[simp] theorem minusToPlusBlockMap_dualSheetLift
    (A : E →L[ℝ] E) :
    minusToPlusBlockMap (E := E) (dualSheetLift (E := E) A) = 0 := by
  ext x
  simp [minusToPlusBlockMap]

omit [CompleteSpace E] in
theorem spectralPlusProj_comp_dualSheetLift
    (A : E →L[ℝ] E) :
    (spectralPlusProj (E := E)).comp (dualSheetLift (E := E) A)
      = (dualSheetLift (E := E) A).comp (spectralPlusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [ContinuousLinearMap.comp_apply, spectralPlusProj_apply_eq_plusPoint]

omit [CompleteSpace E] in
theorem spectralMinusProj_comp_dualSheetLift
    (A : E →L[ℝ] E) :
    (spectralMinusProj (E := E)).comp (dualSheetLift (E := E) A)
      = (dualSheetLift (E := E) A).comp (spectralMinusProj (E := E)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;>
    simp [ContinuousLinearMap.comp_apply, spectralMinusProj_apply_eq_minusPoint]

omit [CompleteSpace E] in
@[simp] theorem plusProjectorFlux_dualSheetLift
    (A : E →L[ℝ] E) :
    plusProjectorFlux (E := E) (dualSheetLift (E := E) A) = 0 := by
  unfold plusProjectorFlux
  rw [spectralPlusProj_comp_dualSheetLift]
  simp

omit [CompleteSpace E] in
@[simp] theorem minusProjectorFlux_dualSheetLift
    (A : E →L[ℝ] E) :
    minusProjectorFlux (E := E) (dualSheetLift (E := E) A) = 0 := by
  unfold minusProjectorFlux
  rw [spectralMinusProj_comp_dualSheetLift]
  simp

end Lift

section MongeAmpere

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- The Hessian metric operator rewritten on the doubled carrier. -/
noncomputable def dualSheetMetricOp
    (H : HessianGeometry E) (x : E) : EndH :=
  dualSheetLift (E := E) (H.metricOp x)

/-- The Monge-Ampère density rewritten as a grading-diagonal doubled operator. -/
noncomputable def mongeAmpereDensityOperator
    (H : HessianGeometry E) (x : E) : EndH :=
  mongeAmpereDensity H x • (1 : EndH)

/-- Basepoint Monge-Ampère density rewritten as a doubled operator. -/
noncomputable def spectralMongeAmpereDensityOperator
    (IST : InfoSpectralTriple E) : EndH :=
  spectralMongeAmpereDensity IST • (1 : EndH)

/-- Operator-valued basepoint Monge-Ampère consistency. -/
def DualSheetMongeAmpereConsistentAtBasepoint
    (IST : InfoSpectralTriple E) : Prop :=
  spectralMongeAmpereDensityOperator (E := E) IST
    = Real.exp (spectralBasepointLogVolume IST) • (1 : EndH)

omit [FiniteDimensional ℝ E] in
@[simp] theorem plusBlockMap_dualSheetMetricOp
    (H : HessianGeometry E) (x : E) :
    plusBlockMap (E := E) (dualSheetMetricOp (E := E) H x) = H.metricOp x := by
  simp [dualSheetMetricOp]

omit [FiniteDimensional ℝ E] in
@[simp] theorem minusBlockMap_dualSheetMetricOp
    (H : HessianGeometry E) (x : E) :
    minusBlockMap (E := E) (dualSheetMetricOp (E := E) H x) = H.metricOp x := by
  simp [dualSheetMetricOp]

omit [FiniteDimensional ℝ E] in
@[simp] theorem plusToMinusBlockMap_dualSheetMetricOp
    (H : HessianGeometry E) (x : E) :
    plusToMinusBlockMap (E := E) (dualSheetMetricOp (E := E) H x) = 0 := by
  simp [dualSheetMetricOp]

omit [FiniteDimensional ℝ E] in
@[simp] theorem minusToPlusBlockMap_dualSheetMetricOp
    (H : HessianGeometry E) (x : E) :
    minusToPlusBlockMap (E := E) (dualSheetMetricOp (E := E) H x) = 0 := by
  simp [dualSheetMetricOp]

omit [FiniteDimensional ℝ E] in
@[simp] theorem plusProjectorFlux_dualSheetMetricOp
    (H : HessianGeometry E) (x : E) :
    plusProjectorFlux (E := E) (dualSheetMetricOp (E := E) H x) = 0 := by
  simp [dualSheetMetricOp]

omit [FiniteDimensional ℝ E] in
@[simp] theorem minusProjectorFlux_dualSheetMetricOp
    (H : HessianGeometry E) (x : E) :
    minusProjectorFlux (E := E) (dualSheetMetricOp (E := E) H x) = 0 := by
  simp [dualSheetMetricOp]

omit [FiniteDimensional ℝ E] in
theorem mongeAmpereDensityOperator_eq_smul_id_of_satisfiesMongeAmpere
    (H : HessianGeometry E) (ρ : E → ℝ)
    (hMA : SatisfiesMongeAmpere H ρ) (x : E) :
    mongeAmpereDensityOperator (E := E) H x = ρ x • (1 : EndH) := by
  simp [mongeAmpereDensityOperator, hMA x]

omit [FiniteDimensional ℝ E] in
theorem mongeAmpereDensityOperator_eq_exp_smul_id_of_satisfiesMongeAmperePotential
    (H : HessianGeometry E) (Φ : E → ℝ)
    (hMA : SatisfiesMongeAmperePotential H Φ) (x : E) :
    mongeAmpereDensityOperator (E := E) H x = Real.exp (Φ x) • (1 : EndH) := by
  simp [mongeAmpereDensityOperator, hMA x]

omit [FiniteDimensional ℝ E] in
theorem mongeAmpereDensityOperator_eq_id_of_incompressible
    (H : HessianGeometry E)
    (hIncomp : IncompressibleMongeAmpere H) (x : E) :
    mongeAmpereDensityOperator (E := E) H x = (1 : EndH) := by
  simpa [mongeAmpereDensityOperator, IncompressibleMongeAmpere] using
    mongeAmpereDensityOperator_eq_smul_id_of_satisfiesMongeAmpere
      (E := E) H (fun _ => (1 : ℝ)) hIncomp x

theorem mongeAmpereDensityOperator_eq_exp_metricLogDet_smul_id
    (H : HessianGeometry E) (x : E)
    (h_det : LinearMap.det (H.metricOp x).toLinearMap ≠ 0) :
    mongeAmpereDensityOperator (E := E) H x
      = Real.exp (metricLogDet H x) • (1 : EndH) := by
  simp [mongeAmpereDensityOperator, mongeAmpereDensity_eq_exp_metricLogDet (H := H) (x := x) h_det]

theorem spectralMongeAmpereDensityOperator_eq_exp_spectralBasepointLogVolume_smul_id
    (IST : InfoSpectralTriple E)
    (h_det : LinearMap.det (IST.H.metricOp IST.x₀).toLinearMap ≠ 0) :
    spectralMongeAmpereDensityOperator (E := E) IST
      = Real.exp (spectralBasepointLogVolume IST) • (1 : EndH) := by
  simp [spectralMongeAmpereDensityOperator,
    spectralMongeAmpereDensity_eq_exp_spectralBasepointLogVolume (IST := IST) h_det]

theorem dualSheetMongeAmpereConsistentAtBasepoint
    (IST : InfoSpectralTriple E)
    (h_det : LinearMap.det (IST.H.metricOp IST.x₀).toLinearMap ≠ 0) :
    DualSheetMongeAmpereConsistentAtBasepoint (E := E) IST := by
  exact spectralMongeAmpereDensityOperator_eq_exp_spectralBasepointLogVolume_smul_id
    (E := E) IST h_det

end MongeAmpere

section CramerRao

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- Cramér-Rao metric operator rewritten on the doubled carrier. -/
noncomputable abbrev cramerRaoDualSheetMetricOp
    (H : HessianGeometry E) (x : E) : EndH :=
  dualSheetMetricOp (E := E) H x

/-- Chiral squeezing rewritten as the doubled-sheet `ε`-boost at scale `2t`. -/
noncomputable def squeezingTransport (t : ℝ) : EndH :=
  epsilonBoost (E := E) (2 * t)

omit [FiniteDimensional ℝ E] in
@[simp] theorem plusBlockMap_squeezingTransport
    (t : ℝ) :
    plusBlockMap (E := E) (squeezingTransport (E := E) t)
      = squeezingEigenPlus t • (1 : E →L[ℝ] E) := by
  ext x
  calc
    plusBlockMap (E := E) (squeezingTransport (E := E) t) x
      = WithLp.fst (epsilonBoost (E := E) (2 * t) (plusPoint (E := E) x)) := by
          simp [plusBlockMap, squeezingTransport]
    _ = Real.cosh (2 * t) • x + Real.sinh (2 * t) • x := by
          simp [epsilonBoost_apply, plusPoint, TomitaTakesaki.modularSignEpsilon, to_doubled]
    _ = (Real.cosh (2 * t) + Real.sinh (2 * t)) • x := by
          simpa using (add_smul (Real.cosh (2 * t)) (Real.sinh (2 * t)) x).symm
    _ = Real.exp (2 * t) • x := by
          rw [Real.cosh_add_sinh]
    _ = (squeezingEigenPlus t • (1 : E →L[ℝ] E)) x := by
          simp [squeezingEigenPlus]

omit [FiniteDimensional ℝ E] in
@[simp] theorem minusBlockMap_squeezingTransport
    (t : ℝ) :
    minusBlockMap (E := E) (squeezingTransport (E := E) t)
      = squeezingEigenMinus t • (1 : E →L[ℝ] E) := by
  ext x
  calc
    minusBlockMap (E := E) (squeezingTransport (E := E) t) x
      = WithLp.snd (epsilonBoost (E := E) (2 * t) (minusPoint (E := E) x)) := by
          simp [minusBlockMap, squeezingTransport]
    _ = Real.cosh (2 * t) • x + -(Real.sinh (2 * t) • x) := by
          simp [epsilonBoost_apply, minusPoint, TomitaTakesaki.modularSignEpsilon, to_doubled]
    _ = (Real.cosh (2 * t) - Real.sinh (2 * t)) • x := by
          simpa [sub_eq_add_neg] using
            (sub_smul (Real.cosh (2 * t)) (Real.sinh (2 * t)) x).symm
    _ = Real.exp (-(2 * t)) • x := by
          rw [Real.cosh_sub_sinh]
    _ = (squeezingEigenMinus t • (1 : E →L[ℝ] E)) x := by
          simp [squeezingEigenMinus]

omit [FiniteDimensional ℝ E] in
@[simp] theorem plusToMinusBlockMap_squeezingTransport
    (t : ℝ) :
    plusToMinusBlockMap (E := E) (squeezingTransport (E := E) t) = 0 := by
  ext x
  simp [plusToMinusBlockMap, squeezingTransport, epsilonBoost_apply,
    plusPoint, TomitaTakesaki.modularSignEpsilon, to_doubled]

omit [FiniteDimensional ℝ E] in
@[simp] theorem minusToPlusBlockMap_squeezingTransport
    (t : ℝ) :
    minusToPlusBlockMap (E := E) (squeezingTransport (E := E) t) = 0 := by
  ext x
  simp [minusToPlusBlockMap, squeezingTransport, epsilonBoost_apply,
    minusPoint, TomitaTakesaki.modularSignEpsilon, to_doubled]

omit [FiniteDimensional ℝ E] in
@[simp] theorem plusProjectorFlux_squeezingTransport
    (t : ℝ) :
    plusProjectorFlux (E := E) (squeezingTransport (E := E) t) = 0 := by
  exact by simpa [squeezingTransport] using plusProjectorFlux_epsilonBoost (E := E) (2 * t)

omit [FiniteDimensional ℝ E] in
@[simp] theorem minusProjectorFlux_squeezingTransport
    (t : ℝ) :
    minusProjectorFlux (E := E) (squeezingTransport (E := E) t) = 0 := by
  exact by simpa [squeezingTransport] using minusProjectorFlux_epsilonBoost (E := E) (2 * t)

end CramerRao

section RNEntropy

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/-- RN entropy source rewritten as a doubled-sheet diagonal scalar operator. -/
noncomputable def rnEntropyDualSheetSourceOp
    (n : Nat) (M : SinkhornMatrix n) : EndH :=
  relativeVolumeChangeRN n M • (1 : EndH)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem plusBlockMap_rnEntropyDualSheetSourceOp
    (n : Nat) (M : SinkhornMatrix n) :
    plusBlockMap (E := E) (rnEntropyDualSheetSourceOp (E := E) n M)
      = relativeVolumeChangeRN n M • (1 : E →L[ℝ] E) := by
  ext x
  simp [plusBlockMap, rnEntropyDualSheetSourceOp]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem minusBlockMap_rnEntropyDualSheetSourceOp
    (n : Nat) (M : SinkhornMatrix n) :
    minusBlockMap (E := E) (rnEntropyDualSheetSourceOp (E := E) n M)
      = relativeVolumeChangeRN n M • (1 : E →L[ℝ] E) := by
  ext x
  simp [minusBlockMap, rnEntropyDualSheetSourceOp]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem plusToMinusBlockMap_rnEntropyDualSheetSourceOp
    (n : Nat) (M : SinkhornMatrix n) :
    plusToMinusBlockMap (E := E) (rnEntropyDualSheetSourceOp (E := E) n M) = 0 := by
  ext x
  simp [plusToMinusBlockMap, rnEntropyDualSheetSourceOp]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem minusToPlusBlockMap_rnEntropyDualSheetSourceOp
    (n : Nat) (M : SinkhornMatrix n) :
    minusToPlusBlockMap (E := E) (rnEntropyDualSheetSourceOp (E := E) n M) = 0 := by
  ext x
  simp [minusToPlusBlockMap, rnEntropyDualSheetSourceOp]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem plusProjectorFlux_rnEntropyDualSheetSourceOp
    (n : Nat) (M : SinkhornMatrix n) :
    plusProjectorFlux (E := E) (rnEntropyDualSheetSourceOp (E := E) n M) = 0 := by
  unfold plusProjectorFlux rnEntropyDualSheetSourceOp
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  have hcomp : (spectralPlusProj (E := E)).comp (1 : EndH) = spectralPlusProj (E := E) := by
    change (spectralPlusProj (E := E)).comp (ContinuousLinearMap.id ℝ H₂) = spectralPlusProj (E := E)
    exact ContinuousLinearMap.comp_id (spectralPlusProj (E := E))
  have hid : (1 : EndH).comp (spectralPlusProj (E := E)) = spectralPlusProj (E := E) := by
    change (ContinuousLinearMap.id ℝ H₂).comp (spectralPlusProj (E := E)) = spectralPlusProj (E := E)
    exact ContinuousLinearMap.id_comp (spectralPlusProj (E := E))
  rw [hcomp, hid]
  simp

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem minusProjectorFlux_rnEntropyDualSheetSourceOp
    (n : Nat) (M : SinkhornMatrix n) :
    minusProjectorFlux (E := E) (rnEntropyDualSheetSourceOp (E := E) n M) = 0 := by
  unfold minusProjectorFlux rnEntropyDualSheetSourceOp
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  have hcomp : (spectralMinusProj (E := E)).comp (1 : EndH) = spectralMinusProj (E := E) := by
    change (spectralMinusProj (E := E)).comp (ContinuousLinearMap.id ℝ H₂) = spectralMinusProj (E := E)
    exact ContinuousLinearMap.comp_id (spectralMinusProj (E := E))
  have hid : (1 : EndH).comp (spectralMinusProj (E := E)) = spectralMinusProj (E := E) := by
    change (ContinuousLinearMap.id ℝ H₂).comp (spectralMinusProj (E := E)) = spectralMinusProj (E := E)
    exact ContinuousLinearMap.id_comp (spectralMinusProj (E := E))
  rw [hcomp, hid]
  simp

omit [FiniteDimensional ℝ E] in
theorem mongeAmpereDensityOperator_eq_rnEntropyDualSheetSourceOp_of_rnEntropySource
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (x : E) :
    mongeAmpereDensityOperator (E := E) Kgeo.H x
      = rnEntropyDualSheetSourceOp (E := E) n M := by
  simp [mongeAmpereDensityOperator, rnEntropyDualSheetSourceOp, hSource x]

omit [FiniteDimensional ℝ E] in
theorem mongeAmpereDensityOperator_eq_exp_neg_kahlerPotentialRN_smul_id_of_rnEntropySource
    (n : Nat)
    (Kgeo : KaehlerInformationGeometry E)
    (M : SinkhornMatrix n)
    (hSource : RNEntropySourcesMongeAmpere n Kgeo M)
    (x : E) :
    mongeAmpereDensityOperator (E := E) Kgeo.H x
      = Real.exp (-kahlerPotentialRN n M) • (1 : EndH) := by
  simp [mongeAmpereDensityOperator, hSource x, relativeVolumeChangeRN]

end RNEntropy

end InfoGeometry.Canonical.MongeAmpereDualSheetBridge

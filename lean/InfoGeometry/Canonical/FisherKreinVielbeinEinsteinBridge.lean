import InfoGeometry.Canonical.SolderingRicciVielbeinBridge
import InfoGeometry.Physics.FisherKreinLorentz
import InfoGeometry.Canonical.ChiralEinsteinBridge
import InfoGeometry.Canonical.SouriauFisherRaoMetric

/-!
# Fisher-Krein, soldering vielbein, and Einstein readouts

This module is the explicit finite bridge between three existing owners:

* `FisherKreinLorentz` supplies the `(-,+,+,+)` Fisher reflection;
* `SolderingSpinConnectionBogoliubov` supplies the `(+,-,-,-)` tetrad metric;
* `RicciMongeAmpere` and `ChiralEinsteinBridge` supply the pointwise Einstein
  tensor and isotropic source equation.

The sign is intentional: the Fisher-Krein reflection is the negative of the
soldering convention.  No identification of an arbitrary Fisher metric with a
spacetime metric is inferred; the split-vielbein calibration remains explicit.
-/

namespace InfoGeometry.Canonical.FisherKreinVielbeinEinsteinBridge

open InfoGeometry.Canonical.SolderingRicciVielbeinBridge
open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.ChiralEinsteinBridge
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Physics.FisherKreinLorentz
open InfoGeometry.Physics.SolderingSpinConnectionBogoliubov
open Matrix

/-- The soldering reference metric is the opposite-sign Fisher-Krein
Lorentz readout. -/
theorem neg_referenceMetric_eq_fisherKreinLorentz4 :
    -referenceMetric = (Matrix.of fisherKreinLorentz4 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [referenceMetric, fisherKreinLorentz4, fisherKreinReflect4,
      fisherUnit4, modularTimeCovector4, delta4, eta4, tetradDiag,
      inducedMetric]; norm_num

/-- The unit soldering tetrad induces the opposite-sign Fisher-Krein metric. -/
theorem neg_unit_tetrad_inducedMetric_eq_fisherKreinLorentz4 :
    -inducedMetric (tetradDiag 1 1 1 1) =
      (Matrix.of fisherKreinLorentz4 : Matrix (Fin 4) (Fin 4) ℝ) := by
  exact neg_referenceMetric_eq_fisherKreinLorentz4

/-- The calibrated positive split leg has the Fisher-Krein time readout. -/
theorem solderingCalibration_plus_eq_fisherKrein_time
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {K : KaehlerInformationGeometry E} {x : E}
    (C : SolderingSplitMetricCalibration K x) :
    K.H.metric x C.ePlus C.ePlus = -fisherKreinLorentz4 0 0 := by
  rw [C.plus_eq_reference]
  have h := congrFun (congrFun neg_referenceMetric_eq_fisherKreinLorentz4 0) 0
  simp at h ⊢
  linarith

/-- The calibrated negative split leg has the Fisher-Krein first spatial
readout. -/
theorem solderingCalibration_minus_eq_fisherKrein_space
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {K : KaehlerInformationGeometry E} {x : E}
    (C : SolderingSplitMetricCalibration K x) :
    K.H.metric x C.eMinus C.eMinus = -fisherKreinLorentz4 1 1 := by
  rw [C.minus_eq_reference]
  have h := congrFun (congrFun neg_referenceMetric_eq_fisherKreinLorentz4 1) 1
  simp at h ⊢
  linarith

/-- The calibrated split legs are Fisher-Krein orthogonal. -/
theorem solderingCalibration_orthogonal_eq_fisherKrein_offdiag
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {K : KaehlerInformationGeometry E} {x : E}
    (C : SolderingSplitMetricCalibration K x) :
    K.H.metric x C.ePlus C.eMinus = fisherKreinLorentz4 0 1 := by
  rw [C.orthogonal_eq_reference]
  have h := congrFun (congrFun neg_referenceMetric_eq_fisherKreinLorentz4 0) 1
  simp at h ⊢
  linarith

/-- A Fisher-Hessian metric identification supplies the soldering split
calibration from normalized positive and negative Fisher directions. -/
noncomputable def fisherHessian_to_solderingCalibration
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (D : InfoGeometry.Canonical.SouriauFisherRaoMetric.Data E)
    (K : KaehlerInformationGeometry E) (x : E)
    (ePlus eMinus : E)
    (hMetric : ∀ u v : E, K.H.metric x u v = D.fisherHessian u v)
    (hPlus : D.fisherHessian ePlus ePlus = 1)
    (hMinus : D.fisherHessian eMinus eMinus = -1)
    (hOrthogonal : D.fisherHessian ePlus eMinus = 0) :
    SolderingSplitMetricCalibration K x := by
  refine
    { ePlus := ePlus
      eMinus := eMinus
      plus_eq_reference := ?_
      minus_eq_reference := ?_
      orthogonal_eq_reference := ?_ }
  · rw [hMetric, hPlus]
    simp [referenceMetric, inducedMetric, tetradDiag, eta4]
  · rw [hMetric, hMinus]
    simp [referenceMetric, inducedMetric, tetradDiag, eta4]
  · rw [hMetric, hOrthogonal]
    simp [referenceMetric, inducedMetric, tetradDiag, eta4]

/-- Under Einstein-Kähler proportionality, transported calibrated split legs
retain the metric-proportional Einstein tensor readout. -/
theorem einsteinTensor_transport_calibrated_split
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (c : ℝ) (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar : ℝ) (C : SolderingSplitMetricCalibration K x)
    (Γ : SpinConnection K x C.toSplitVielbein)
    (hEin : IsEinsteinKaehlerAtWith c R K x) :
    einsteinTensorAt R K x scalar
        (Γ.transport C.toSplitVielbein.ePlus)
        (Γ.transport C.toSplitVielbein.eMinus) =
      (c - scalar / 2) * K.H.metric x
        (Γ.transport C.toSplitVielbein.ePlus)
        (Γ.transport C.toSplitVielbein.eMinus) := by
  exact einsteinTensor_transport_split_eq_metric_multiple
    c R K x scalar C.toSplitVielbein Γ hEin

end InfoGeometry.Canonical.FisherKreinVielbeinEinsteinBridge

import InfoGeometry.Canonical.RicciMongeAmpere
import InfoGeometry.Physics.SolderingSpinConnectionBogoliubov

/-!
# Soldering to Ricci split-vielbein bridge

The soldering owner supplies a concrete matrix metric, while the Ricci owner
uses the abstract `SplitVielbein` structure.  This file is the small typed
interface between them.  The metric agreement is an explicit property:
the matrix soldering construction does not by itself identify an arbitrary
information-geometry metric with that matrix.
-/

namespace InfoGeometry.Canonical.SolderingRicciVielbeinBridge

open InfoGeometry.Canonical.RicciMongeAmpere
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Physics.SolderingSpinConnectionBogoliubov

noncomputable section

abbrev SolderingMetric := Matrix (Fin 4) (Fin 4) ℝ

/-- The reference metric induced by the unit diagonal soldering tetrad. -/
def referenceMetric : SolderingMetric :=
  inducedMetric (tetradDiag 1 1 1 1)

@[simp] theorem referenceMetric_apply_zero_zero :
    referenceMetric 0 0 = 1 := by
  simp [referenceMetric, inducedMetric_diag]

@[simp] theorem referenceMetric_apply_one_one :
    referenceMetric 1 1 = -1 := by
  simp [referenceMetric, inducedMetric_diag]

@[simp] theorem referenceMetric_apply_zero_one :
    referenceMetric 0 1 = 0 := by
  simp [referenceMetric, inducedMetric_diag]

/-!
A calibration records precisely the three metric readouts needed by the
abstract split-vielbein carrier.  The vectors remain native vectors in `E`;
only their calibrated metric values are identified with soldering entries.
-/
structure SolderingSplitMetricCalibration
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (K : KaehlerInformationGeometry E) (x : E) where
  ePlus : E
  eMinus : E
  plus_eq_reference : K.H.metric x ePlus ePlus = referenceMetric 0 0
  minus_eq_reference : K.H.metric x eMinus eMinus = referenceMetric 1 1
  orthogonal_eq_reference : K.H.metric x ePlus eMinus = referenceMetric 0 1

/-- A calibrated soldering frame is a genuine Ricci `SplitVielbein`. -/
def SolderingSplitMetricCalibration.toSplitVielbein
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {K : KaehlerInformationGeometry E} {x : E}
    (C : SolderingSplitMetricCalibration K x) : SplitVielbein K x where
  ePlus := C.ePlus
  eMinus := C.eMinus
  plus_norm := by simpa using C.plus_eq_reference
  minus_norm := by simpa using C.minus_eq_reference
  orthogonal := by simpa using C.orthogonal_eq_reference

@[simp] theorem toSplitVielbein_ePlus
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {K : KaehlerInformationGeometry E} {x : E}
    (C : SolderingSplitMetricCalibration K x) :
    C.toSplitVielbein.ePlus = C.ePlus := rfl

@[simp] theorem toSplitVielbein_eMinus
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {K : KaehlerInformationGeometry E} {x : E}
    (C : SolderingSplitMetricCalibration K x) :
    C.toSplitVielbein.eMinus = C.eMinus := rfl

end
end InfoGeometry.Canonical.SolderingRicciVielbeinBridge

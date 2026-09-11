import InfoGeometry.Canonical.ChiralEinsteinBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.ChiralGravity

open InfoGeometry.Canonical.ChiralAnomaly
open InfoGeometry.Canonical.ChiralEinsteinBridge
open InfoGeometry.Canonical.KaehlerGeometry
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.RicciMongeAmpere

section CurvatureForcing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Einstein residual evaluated against the anomaly-sourced stress-energy model.
-/
noncomputable def anomalyEinsteinResidualAt
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ) (u v : E) : ℝ :=
  einsteinTensorAt R K x scalar u v + Λ * K.H.metric x u v

@[simp] lemma anomalyEinsteinResidualAt_def
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ) (u v : E) :
    anomalyEinsteinResidualAt R K x scalar Λ u v
      = einsteinTensorAt R K x scalar u v + Λ * K.H.metric x u v := rfl

/-- Residual closure: vacuum Einstein implies the anomaly residual vanishes. -/
theorem anomalyEinsteinResidualAt_vanishes_of_vacuum
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (hVac : VacuumEinsteinEquationAt R K x scalar Λ)
    (u v : E) :
    anomalyEinsteinResidualAt R K x scalar Λ u v = 0 := by
  unfold anomalyEinsteinResidualAt
  simpa using hVac u v

/-- Canonical curvature-forcing state at a given pair of directions. -/
def AnomalyCurvatureForcingStateAt
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ) (u v : E) : Prop :=
  anomalyEinsteinResidualAt R K x scalar Λ u v ≠ 0

/--
Under anomaly-sourced Einstein equation, residual equals `κ * A * g`.
-/
lemma anomalyEinsteinResidual_eq_kappa_mul_metric
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ κ A : ℝ)
    (hEinEq : EinsteinEquationAt R K x scalar Λ κ (anomalyStressEnergyAt K x A))
    (u v : E) :
    anomalyEinsteinResidualAt R K x scalar Λ u v = κ * A * K.H.metric x u v := by
  unfold anomalyEinsteinResidualAt
  calc
    einsteinTensorAt R K x scalar u v + Λ * K.H.metric x u v
      = κ * anomalyStressEnergyAt K x A u v := hEinEq u v
    _ = κ * A * K.H.metric x u v := by
      simp [anomalyStressEnergyAt, mul_assoc]

/--
If anomaly amplitude `A` and coupling `κ` are nonzero, Einstein residual
on the split `plus` leg is nonzero: anomaly forces curvature.
-/
theorem anomaly_nonzero_forces_curved_plus_component
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ κ A : ℝ)
    (hEinEq : EinsteinEquationAt R K x scalar Λ κ (anomalyStressEnergyAt K x A))
    (V : SplitVielbein K x)
    (hκ : κ ≠ 0) (hA : A ≠ 0) :
    AnomalyCurvatureForcingStateAt R K x scalar Λ V.ePlus V.ePlus := by
  unfold AnomalyCurvatureForcingStateAt
  rw [anomalyEinsteinResidual_eq_kappa_mul_metric
      (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
      (κ := κ) (A := A) hEinEq]
  rw [V.plus_norm, mul_one]
  exact mul_ne_zero hκ hA

/--
Nonzero anomaly source excludes the vacuum Einstein equation on split frames.
-/
theorem anomaly_nonzero_excludes_vacuum
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ κ A : ℝ)
    (hEinEq : EinsteinEquationAt R K x scalar Λ κ (anomalyStressEnergyAt K x A))
    (V : SplitVielbein K x)
    (hκ : κ ≠ 0) (hA : A ≠ 0) :
    ¬ VacuumEinsteinEquationAt R K x scalar Λ := by
  intro hVac
  have hcurved :
      anomalyEinsteinResidualAt R K x scalar Λ V.ePlus V.ePlus ≠ 0 :=
    anomaly_nonzero_forces_curved_plus_component
      (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
      (κ := κ) (A := A) hEinEq V hκ hA
  exact hcurved (by
    unfold anomalyEinsteinResidualAt
    simpa using hVac V.ePlus V.ePlus)

end CurvatureForcing

section RoutingSource

variable (n : Nat)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Routing-anomaly specialization:
if `A = ε_route` is nonzero, it forces non-vacuum curvature on split `plus` leg.
-/
theorem routingAnomaly_nonzero_forces_curved_plus_component
    (R : RicciTensor E) (K : KaehlerInformationGeometry E) (x : E)
    (scalar Λ κ : ℝ)
    (w : PermMode n → ℝ) (label : PermMode n → CliffordLabel)
    (hEinEq : EinsteinEquationAt R K x scalar Λ κ
      (anomalyStressEnergyModelAt K x (routingEpsilon w label)))
    (V : SplitVielbein K x)
    (hκ : κ ≠ 0)
    (hε : routingEpsilon w label ≠ 0) :
    AnomalyCurvatureForcingStateAt R K x scalar Λ V.ePlus V.ePlus := by
  exact anomaly_nonzero_forces_curved_plus_component
    (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
    (κ := κ) (A := routingEpsilon w label) hEinEq V hκ hε

end RoutingSource

end InfoGeometry.Canonical.ChiralGravity

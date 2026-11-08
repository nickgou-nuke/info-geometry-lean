/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.IncompressibleBitBridge
import InfoGeometry.Clifford.Grading

namespace InfoGeometry.Canonical.ChiralCliffordBridge

open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.Drazin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Difference of the Moore–Penrose right and left projectors.

This operator is not assumed to be an involution or a Clifford grading. -/
noncomputable def chiralGrading (CI : ConformalInference E) : E →L[ℝ] E :=
  let P_R := IsMoorePenroseInverse.rightProjector CI.A CI.A_MP
  let P_L := IsMoorePenroseInverse.leftProjector CI.A CI.A_MP
  P_R - P_L

/-- Half-sum of the spectral chiral projector and the projector difference.

No idempotency claim is made for this operator. -/
noncomputable def generalizedChiralPlus (CI : ConformalInference E) : E →L[ℝ] E :=
  ((2 : ℝ)⁻¹) • (CI.spectralChiralProjector + chiralGrading CI)

/-- Half-difference of the spectral chiral projector and the projector difference.

No idempotency claim is made for this operator. -/
noncomputable def generalizedChiralMinus (CI : ConformalInference E) : E →L[ℝ] E :=
  ((2 : ℝ)⁻¹) • (CI.spectralChiralProjector - chiralGrading CI)

/-! ### Cartan Decomposition of the Information Algebra -/

/-- Operators commuting with the Moore–Penrose projector difference. -/
def IsCompactBeliefUpdate (CI : ConformalInference E) (X : E →L[ℝ] E) : Prop :=
  X * chiralGrading CI = chiralGrading CI * X

/-- Operators anti-commuting with the Moore–Penrose projector difference. -/
def IsNonCompactBeliefUpdate (CI : ConformalInference E) (X : E →L[ℝ] E) : Prop :=
  X * chiralGrading CI = - (chiralGrading CI * X)

omit [FiniteDimensional ℝ E] in
/-- The anomaly is the commutator of the two chiral projectors. -/
theorem chiralAnomaly_eq_projector_commutator (CI : ConformalInference E) :
    CI.chiralAnomaly
      = CI.spectralChiralProjector * CI.metricChiralProjector
          - CI.metricChiralProjector * CI.spectralChiralProjector := by
  simp [ConformalInference.chiralAnomaly, ConformalInference.spectralChiralProjector,
    ConformalInference.metricChiralProjector]

omit [FiniteDimensional ℝ E] in
/-- Normal inference forces the two chiral projectors to commute. -/
theorem cartan_collapse_of_normal (CI : ConformalInference E) (h_norm : CI.IsNormalInference) :
    CI.chiralAnomaly = 0 := by
  have hActionZero : CI.unitOfAction = 0 :=
    CI.unitOfAction_eq_zero_of_normalInference h_norm
  have hNormZero : ‖CI.actionStructureConstantOp‖ = 0 := by
    simpa [ConformalInference.unitOfAction] using hActionZero
  have hActionOpZero : CI.actionStructureConstantOp = 0 :=
    norm_eq_zero.mp hNormZero
  have hAnomZero : CI.chiralAnomalyOperator = 0 := by
    simpa [CI.actionStructureConstantOp_eq_chiralAnomalyOperator] using hActionOpZero
  simpa [ConformalInference.chiralAnomalyOperator] using hAnomZero


omit [FiniteDimensional ℝ E] in
/--
Unit relative volume collapses the Cartan anomaly through the normality bridge.
-/
theorem cartan_collapse_of_unitRelativeVolume
    {n : Nat}
    (CI : ConformalInference E)
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = InfoGeometry.Canonical.MoE.kahlerPotentialRN n M)
    (hUnitVolume : InfoGeometry.Canonical.MoE.relativeVolumeChangeRN n M = 1) :
    CI.chiralAnomaly = 0 := by
  have hNormal : CI.IsNormalInference :=
    CI.isNormalInference_of_kahlerLogDet_unitRelativeVolume
      (M := M) hScaleFromKahler hUnitVolume
  exact cartan_collapse_of_normal CI hNormal

omit [FiniteDimensional ℝ E] in
/--
Proof-carrying unit-relative-volume route for Cartan anomaly collapse.

This is the constructive companion to `cartan_collapse_of_unitRelativeVolume`:
callers supply the `UnitRelativeVolumeBit` witness packet rather than a bare
`relativeVolumeChangeRN n M = 1` equality.
-/
theorem cartan_collapse_of_unitRelativeVolumeBit
    {n : Nat}
    (CI : ConformalInference E)
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = InfoGeometry.Canonical.MoE.kahlerPotentialRN n M)
    (bit : InfoGeometry.Canonical.IncompressibleBitBridge.UnitRelativeVolumeBit n M) :
    CI.chiralAnomaly = 0 := by
  have hNormal : CI.IsNormalInference :=
    InfoGeometry.Canonical.IncompressibleBitBridge.isNormalInference_of_unitRelativeVolumeBit
      (CI := CI) (M := M) hScaleFromKahler bit
  exact cartan_collapse_of_normal CI hNormal

end InfoGeometry.Canonical.ChiralCliffordBridge

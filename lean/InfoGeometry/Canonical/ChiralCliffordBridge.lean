import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.IncompressibleBitBridge
import InfoGeometry.Clifford.Grading

namespace InfoGeometry.Canonical.ChiralCliffordBridge

open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.Drazin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
The Chiral Grading Operator Γ associated with a degenerate information operator A.
In the Cl(1,1) limit, this corresponds to the grading involution.
Formally defined from the Right and Left Penrose projectors: Γ = P_R - P_L.
This measures the geometric asymmetry between information gain and retrieval.
-/
noncomputable def chiralGrading (CI : ConformalInference E) : E →L[ℝ] E :=
  let P_R := IsMoorePenroseInverse.rightProjector CI.A CI.A_MP
  let P_L := IsMoorePenroseInverse.leftProjector CI.A CI.A_MP
  P_R - P_L

/--
Generalized Chiral Projectors for the Information Space.
P± = (P_D ± Γ) / 2.
These projectors isolate the belief states that are aligned/anti-aligned 
with the geometric-spectral mismatch.
-/
noncomputable def generalizedChiralPlus (CI : ConformalInference E) : E →L[ℝ] E :=
  ((2 : ℝ)⁻¹) • (CI.spectralChiralProjector + chiralGrading CI)

/-- Definition `generalizedChiralMinus`. -/
noncomputable def generalizedChiralMinus (CI : ConformalInference E) : E →L[ℝ] E :=
  ((2 : ℝ)⁻¹) • (CI.spectralChiralProjector - chiralGrading CI)

/-! ### Cartan Decomposition of the Information Algebra -/

/--
The Compact (Rotational) Sector 𝔨.
Information operators that commute with the chiral grading Γ.
These preserve the chirality of the belief manifold.
-/
def IsCompactBeliefUpdate (CI : ConformalInference E) (X : E →L[ℝ] E) : Prop :=
  X * chiralGrading CI = chiralGrading CI * X

/--
The Non-Compact (Boost) Sector 𝔭.
Information operators that anti-commute with the chiral grading Γ.
These are the generators of the RG flow and the emergent scale ε.
-/
def IsNonCompactBeliefUpdate (CI : ConformalInference E) (X : E →L[ℝ] E) : Prop :=
  X * chiralGrading CI = - (chiralGrading CI * X)

omit [FiniteDimensional ℝ E] in
/--
Theorem: The Chiral Anomaly χ = [P_D, P_MP] acts as the
fundamental structure constant (the ε) of the Cartan decomposition.
This bridges the Conformal generators to the Clifford grading.
-/
theorem anomaly_as_structure_constant (CI : ConformalInference E) :
    CI.chiralAnomaly
      = CI.spectralChiralProjector * CI.metricChiralProjector
          - CI.metricChiralProjector * CI.spectralChiralProjector := by
  simp [ConformalInference.chiralAnomaly, ConformalInference.spectralChiralProjector,
    ConformalInference.metricChiralProjector]

omit [FiniteDimensional ℝ E] in
/--
Specialization: If the information flow is normal, the Cartan decomposition 
collapses because Γ and P_D coincide or commute.
-/
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

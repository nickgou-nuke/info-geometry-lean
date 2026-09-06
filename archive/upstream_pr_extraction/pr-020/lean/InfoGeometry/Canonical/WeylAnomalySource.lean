import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.ConformalAlgebra
import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Canonical.RicciMongeAmpere

set_option linter.unusedSectionVars false

/-!
# InfoGeometry.Canonical.WeylAnomalySource

Constructive Weyl-gauge anomaly-source layer:

- nonzero chiral anomaly implies a chiral inference state
- anomaly sourcing forces nonzero transported Einstein residual
- Cartan/Weyl closure reuses the same anomaly-source trunk
-/

namespace InfoGeometry.Canonical.WeylInformationGauge

open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.ConformalAlgebra
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.RicciMongeAmpere

section DilationSource

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Nonzero chiral-anomaly operator implies positive chiral scale (`IsChiralInference`).
-/
theorem chiralInferenceState_of_nonzero_anomaly
    (CI : ConformalInference E)
    (hAnom : CI.chiralAnomalyOperator ≠ 0) :
    CI.IsChiralInference := by
  unfold ConformalInference.IsChiralInference
  rw [CI.chiralScale_eq_projectorObstruction_nnnorm]
  simpa [ConformalInference.projectorObstruction] using
    (NNReal.coe_pos).2 ((nnnorm_pos).2 hAnom)

/--
Dilation/anomaly sourcing statement:
if the induced chemical potential equals the chiral scale and the conformal
state is chiral, then the transported Einstein residual is nonzero.
-/
private theorem dilationAnomaly_sources_transportedEinsteinResidual
    (CI : ConformalInference E)
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hSource :
      transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = CI.chiralScale)
    (hChiral : CI.IsChiralInference) :
    transportedEinsteinResidual (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) V Γ ≠ 0 := by
  have hμ_ne :
      transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ ≠ 0 := by
    rw [hSource]
    exact ne_of_gt hChiral
  exact hμ_ne

/--
Strong sourcing form:
nonzero anomaly plus source relation forces nonzero transported Einstein residual.
-/
theorem nonzeroAnomaly_sources_transportedEinsteinResidual
    (CI : ConformalInference E)
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hSource :
      transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = CI.chiralScale)
    (hAnom : CI.chiralAnomalyOperator ≠ 0) :
    transportedEinsteinResidual (R := R) (K := K) (x := x)
      (scalar := scalar) (Λ := Λ) V Γ ≠ 0 := by
  exact dilationAnomaly_sources_transportedEinsteinResidual
    (CI := CI) (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
    (V := V) (Γ := Γ) hSource
    (chiralInferenceState_of_nonzero_anomaly (CI := CI) hAnom)

end DilationSource

section CartanWeylClosure

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Cartan generator split specialized to Weyl-gauge interpretation:
`M` is volume-preserving and `D` is Weyl-dilation.
-/
private theorem cartanWeyl_generator_split
    (CBA : ConformalBeliefAlgebra E)
    (hCartan : CBA.GeneratorCartanDecomposition) :
    CBA.IsVolumePreservingPart CBA.M ∧ CBA.IsWeylDilationPart CBA.D := by
  exact CBA.cartan_generator_split hCartan

/--
Cartan/Weyl closure theorem:
if the conformal generators satisfy the Cartan split and the transported Einstein
residual is sourced by the chiral scale, then any nonzero anomaly forces a
nonzero transported Einstein residual.
-/
private theorem cartanWeyl_dilation_sources_transportedEinsteinResidual
    (CBA : ConformalBeliefAlgebra E)
    (hCartan : CBA.GeneratorCartanDecomposition)
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hSource :
      transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = CBA.CI.chiralScale)
    (hAnom : CBA.CI.chiralAnomalyOperator ≠ 0) :
    CBA.IsVolumePreservingPart CBA.M
      ∧ CBA.IsWeylDilationPart CBA.D
      ∧ transportedEinsteinResidual (R := R) (K := K) (x := x)
          (scalar := scalar) (Λ := Λ) V Γ ≠ 0 := by
  refine ⟨(CBA.M_in_volumePreserving_of_cartan hCartan),
    (CBA.D_in_weylDilation_of_cartan hCartan), ?_⟩
  exact nonzeroAnomaly_sources_transportedEinsteinResidual
    (CI := CBA.CI) (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
    (V := V) (Γ := Γ) hSource hAnom

/--
Cartan/Weyl closure in primitive form (no bundled split witness):
given explicit compact/non-compact sector hypotheses for `(M,D)`, nonzero
anomaly still forces nonzero transported Einstein residual under the same
source relation.
-/
private theorem cartanWeyl_dilation_sources_transportedEinsteinResidual_of_parts
    (CBA : ConformalBeliefAlgebra E)
    (hM : CBA.IsVolumePreservingPart CBA.M)
    (hD : CBA.IsWeylDilationPart CBA.D)
    (R : RicciTensor E)
    (K : InfoGeometry.Canonical.KaehlerGeometry.KaehlerInformationGeometry E) (x : E)
    (scalar Λ : ℝ)
    (V : SplitVielbein K x) (Γ : SpinConnection K x V)
    (hSource :
      transportedEinsteinResidual (R := R) (K := K) (x := x)
        (scalar := scalar) (Λ := Λ) V Γ = CBA.CI.chiralScale)
    (hAnom : CBA.CI.chiralAnomalyOperator ≠ 0) :
    CBA.IsVolumePreservingPart CBA.M
      ∧ CBA.IsWeylDilationPart CBA.D
      ∧ transportedEinsteinResidual (R := R) (K := K) (x := x)
          (scalar := scalar) (Λ := Λ) V Γ ≠ 0 := by
  refine ⟨hM, hD, ?_⟩
  exact nonzeroAnomaly_sources_transportedEinsteinResidual
    (CI := CBA.CI) (R := R) (K := K) (x := x) (scalar := scalar) (Λ := Λ)
    (V := V) (Γ := Γ) hSource hAnom

end CartanWeylClosure

end InfoGeometry.Canonical.WeylInformationGauge

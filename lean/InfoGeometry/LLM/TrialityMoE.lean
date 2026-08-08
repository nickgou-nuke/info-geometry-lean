import InfoGeometry.Canonical.ObserverDefect
import InfoGeometry.Canonical.ModularSourceBridge
import InfoGeometry.Canonical.KKTClosureSymmetry
import InfoGeometry.Canonical.RelativePotentialCore
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.Architecture

open scoped BigOperators InnerProductSpace

namespace InfoGeometry.LLM.TrialityMoE

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ObserverDefect
open InfoGeometry.Canonical.ModularSourceBridge

section ResidualBlock

variable {H : Type*} [AddCommMonoid H]

/--
Llama-style two-stage residual block:
1) attention pre-norm and residual add,
2) feed-forward pre-norm and residual add.
-/
structure TwoStageResidualBlock where
  attentionNorm : H → H
  feedForwardNorm : H → H
  attention : H → H
  feedForward : H → H

namespace TwoStageResidualBlock

/-- `h = x + attention(attentionNorm x)` -/
def afterAttention (B : TwoStageResidualBlock (H := H)) (x : H) : H :=
  x + B.attention (B.attentionNorm x)

/-- `out = h + feedForward(feedForwardNorm h)` -/
def afterFeedForward (B : TwoStageResidualBlock (H := H)) (x : H) : H :=
  let h := B.afterAttention x
  h + B.feedForward (B.feedForwardNorm h)

/-- Full block update. -/
def run (B : TwoStageResidualBlock (H := H)) (x : H) : H :=
  B.afterFeedForward x

/--
Exact two-stage residual law matching the extracted Llama 4 transformer block form.
-/
@[rep_depth transport]
theorem two_stage_residual_block_update (B : TwoStageResidualBlock (H := H)) (x : H) :
    B.run x =
      let h := x + B.attention (B.attentionNorm x)
      h + B.feedForward (B.feedForwardNorm h) := by
  rfl

end TwoStageResidualBlock

end ResidualBlock

section MoEAlgebra

variable {X V E : Type*} [Fintype E] [DecidableEq E]
variable [AddCommMonoid V] [Module ℝ V]

/-- Sparse routing interface: active-set predicate plus a hard-zero law off the active set. -/
structure SparseRouter where
  weight : X → E → ℝ
  gate : X → E → Bool
  inactive_weight_eq_zero : ∀ x e, gate x e = false → weight x e = 0

namespace SparseRouter

/-- Active-gated weight. -/
def activeWeight (R : SparseRouter (X := X) (E := E)) (x : X) (e : E) : ℝ :=
  if R.gate x e then R.weight x e else 0

/-- Defect-gated weight (inactive complement). -/
def defectWeight (R : SparseRouter (X := X) (E := E)) (x : X) (e : E) : ℝ :=
  if R.gate x e then 0 else R.weight x e

section OmitRouterTypeclasses

omit [Fintype E] [DecidableEq E]

/-- Pointwise router split into active and defect contributions. -/
@[rep_depth transport]
theorem router_weight_split (R : SparseRouter (X := X) (E := E)) (x : X) (e : E) :
    R.weight x e = R.activeWeight x e + R.defectWeight x e := by
  cases hGate : R.gate x e with
  | false =>
      simp [activeWeight, defectWeight, hGate, R.inactive_weight_eq_zero x e hGate]
  | true =>
      simp [activeWeight, defectWeight, hGate]

@[simp]
theorem activeWeight_eq_weight
    (R : SparseRouter (X := X) (E := E)) (x : X) (e : E) :
    R.activeWeight x e = R.weight x e := by
  cases hGate : R.gate x e with
  | false =>
      simp [activeWeight, hGate, R.inactive_weight_eq_zero x e hGate]
  | true =>
      simp [activeWeight, hGate]

@[simp]
theorem defectWeight_eq_zero
    (R : SparseRouter (X := X) (E := E)) (x : X) (e : E) :
    R.defectWeight x e = 0 := by
  cases hGate : R.gate x e with
  | false =>
      simp [defectWeight, hGate, R.inactive_weight_eq_zero x e hGate]
  | true =>
      simp [defectWeight, hGate]

end OmitRouterTypeclasses

end SparseRouter

/-- MoE block as router plus expert family. -/
structure TrialityMoEBlock where
  router : SparseRouter (X := X) (E := E)
  expert : E → X → V

namespace TrialityMoEBlock

/-- Generic weighted expert aggregation. -/
def weightedOutput (B : TrialityMoEBlock (X := X) (V := V) (E := E))
    (w : X → E → ℝ) (x : X) : V :=
  ∑ e, (w x e) • B.expert e x

/-- Total MoE output from raw router weights. -/
def totalOutput (B : TrialityMoEBlock (X := X) (V := V) (E := E)) (x : X) : V :=
  B.weightedOutput B.router.weight x

/-- Active MoE output restricted to the active gate. -/
def activeOutput (B : TrialityMoEBlock (X := X) (V := V) (E := E)) (x : X) : V :=
  B.weightedOutput B.router.activeWeight x

/-- Defect MoE output restricted to the inactive gate. -/
def defectOutput (B : TrialityMoEBlock (X := X) (V := V) (E := E)) (x : X) : V :=
  B.weightedOutput B.router.defectWeight x

section OmitDecidableEqMoE

omit [DecidableEq E]

/-- Algebraic MoE split: total output equals active plus defect output. -/
@[rep_depth transport]
theorem moe_output_split (B : TrialityMoEBlock (X := X) (V := V) (E := E)) (x : X) :
    B.totalOutput x = B.activeOutput x + B.defectOutput x := by
  unfold totalOutput activeOutput defectOutput weightedOutput
  calc
    ∑ e, (B.router.weight x e) • B.expert e x
        = ∑ e, ((B.router.activeWeight x e + B.router.defectWeight x e) • B.expert e x) := by
            refine Finset.sum_congr rfl ?_
            intro e _
            rw [B.router.router_weight_split x e]
    _ = ∑ e, ((B.router.activeWeight x e) • B.expert e x + (B.router.defectWeight x e) • B.expert e x) := by
          refine Finset.sum_congr rfl ?_
          intro e _
          simp
    _ = (∑ e, (B.router.activeWeight x e) • B.expert e x)
          + (∑ e, (B.router.defectWeight x e) • B.expert e x) := by
          rw [Finset.sum_add_distrib]

@[simp] theorem defectOutput_eq_zero
    (B : TrialityMoEBlock (X := X) (V := V) (E := E)) (x : X) :
    B.defectOutput x = 0 := by
  unfold defectOutput weightedOutput
  simp [SparseRouter.defectWeight_eq_zero]

/-- Under hard-zero inactive routing, total routed output equals active routed output. -/
@[rep_depth transport]
theorem totalOutput_eq_activeOutput
    (B : TrialityMoEBlock (X := X) (V := V) (E := E)) (x : X) :
    B.totalOutput x = B.activeOutput x := by
  calc
    B.totalOutput x = B.activeOutput x + B.defectOutput x := B.moe_output_split x
    _ = B.activeOutput x := by simp

end OmitDecidableEqMoE

end TrialityMoEBlock

/--
MoE output surface with explicit shared path plus routed expert path.
Mirrors `out = shared(x) + routed(x)` from vendor implementations.
-/
structure SharedRoutedMoEBlock where
  shared : X → V
  routed : TrialityMoEBlock (X := X) (V := V) (E := E)

namespace SharedRoutedMoEBlock

/-- Full output: shared path plus routed path. -/
def output (B : SharedRoutedMoEBlock (X := X) (V := V) (E := E)) (x : X) : V :=
  B.shared x + B.routed.totalOutput x

section OmitDecidableEqSharedRouted

omit [DecidableEq E]

/-- Shared + routed decomposition into active and defect routed parts. -/
@[rep_depth transport]
theorem output_split_active_defect
    (B : SharedRoutedMoEBlock (X := X) (V := V) (E := E)) (x : X) :
    B.output x = (B.shared x + B.routed.activeOutput x) + B.routed.defectOutput x := by
  unfold output
  rw [B.routed.moe_output_split x]
  simp

/-- In hard-zero sparse routing, output reduces to shared + active routed contribution. -/
@[rep_depth transport]
theorem output_eq_shared_plus_active
    (B : SharedRoutedMoEBlock (X := X) (V := V) (E := E)) (x : X) :
    B.output x = B.shared x + B.routed.activeOutput x := by
  unfold output
  rw [B.routed.totalOutput_eq_activeOutput x]

end OmitDecidableEqSharedRouted

end SharedRoutedMoEBlock

end MoEAlgebra

section CanonicalBridge

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Bridge property linking an LLM router-residual operator to the canonical observer-defect residual.
-/
structure RouterDefectBridge where
  CIK : CertifiedInverseKernel H₂
  obs : ObserverL5 CIK
  flow : BackgroundModularFlow CIK
  routerResidual : EndH
  residual_eq_observerDefect :
    routerResidual = observerDefectResidual CIK obs

namespace RouterDefectBridge

/--
Canonical theorem-backed constructor for the router/observer bridge.

This is the preferred constructor on the closure lane: the router residual is not
postulated independently, but taken to be the canonical observer-defect residual.
-/
noncomputable def ofCanonicalObserverDefect
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK) :
    RouterDefectBridge (E := E) :=
  { CIK := CIK
    obs := obs
    flow := flow
    routerResidual := observerDefectResidual CIK obs
    residual_eq_observerDefect := rfl }

@[simp] theorem ofCanonicalObserverDefect_routerResidual
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK) :
    (ofCanonicalObserverDefect (E := E) CIK obs flow).routerResidual = observerDefectResidual CIK obs := by
  rfl

/-- Sourced generator built from the LLM-side residual input. -/
noncomputable def sourcedGenerator (B : RouterDefectBridge (E := E)) : EndH :=
  B.flow.K0 + B.routerResidual

/-- LLM-side sourced generator coincides with canonical sourced modular generator under bridge equality. -/
@[bridge_target_tag, rep_depth transport]
theorem sourcedGenerator_eq_canonical (B : RouterDefectBridge (E := E)) :
    B.sourcedGenerator = sourcedModularGenerator B.CIK B.obs B.flow := by
  unfold sourcedGenerator sourcedModularGenerator
  simp [B.residual_eq_observerDefect]

/-- Drazin-cut preservation follows immediately once the router residual is identified canonically. -/
@[bridge_target_tag, rep_depth transport]
theorem sourcedGenerator_respects_cut (B : RouterDefectBridge (E := E)) :
    Commute B.sourcedGenerator B.CIK.spectralComplementaryProjector := by
  rw [sourcedGenerator_eq_canonical (B := B)]
  exact sourcedModularGenerator_respects_spectral_cut (CIK := B.CIK) (obs := B.obs) (flow := B.flow)

end RouterDefectBridge

/--
Bounded bridge variant: the router residual is controlled by the canonical
defect-central channel `Z_D` on the same Drazin/KKT lane.

Legacy ambient-norm shim. This is retained for old local consumers only; the
active D3 closure surface is `RouterDefectThermodynamicBridge`, where comparison
is performed through the Weyl/relative-potential readout lane.
-/
structure RouterDefectBoundBridge where
  CIK : CertifiedInverseKernel H₂
  flow : BackgroundModularFlow CIK
  routerResidual : EndH
  residual_norm_le_ZD :
    ‖routerResidual‖ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖

namespace RouterDefectBoundBridge

/--
Weyl/thermodynamic comparison packet for two operators.

This is the repo-native replacement for using an ambient operator norm as the
information-geometric comparison. An operator is first sent through an explicit
information-geometric readout, and that readout must be identified with the
normalized relative information norm from the RedLine corridor. The norm is the
RMS size of `-log(dμ / dν)` on projective positive states, measured against the
reference gauge; no ambient operator norm or base-space geometry is assumed.
-/
@[rep_depth transport]
structure WeylThermodynamicOperatorComparison
    (residual central : EndH) where
  α : Type
  fintype : Fintype α
  nonempty : Nonempty α
  operatorInformationNormReadout : EndH → ℝ
  defectRay : InfoGeometry.Canonical.PositiveRayCore.PositiveRay α
  centralRay : InfoGeometry.Canonical.PositiveRayCore.PositiveRay α
  referenceRay : InfoGeometry.Canonical.PositiveRayCore.PositiveRay α
  residual_readout_eq_relativeInformationNorm :
    operatorInformationNormReadout residual =
      @InfoGeometry.Canonical.RelativePotentialCore.relativeInformationNorm
        α fintype nonempty defectRay referenceRay
  central_readout_eq_relativeInformationNorm :
    operatorInformationNormReadout central =
      @InfoGeometry.Canonical.RelativePotentialCore.relativeInformationNorm
        α fintype nonempty centralRay referenceRay
  relativeInformationNorm_le_central :
    @InfoGeometry.Canonical.RelativePotentialCore.relativeInformationNorm
        α fintype nonempty defectRay referenceRay
      ≤
    @InfoGeometry.Canonical.RelativePotentialCore.relativeInformationNorm
        α fintype nonempty centralRay referenceRay

omit [CompleteSpace E] in
/--
Readout-level consequence of a Weyl/thermodynamic comparison packet.

The result is an inequality between explicitly represented information-geometric
relative norms, not an ambient norm inequality between operators.
-/
@[rep_depth transport]
theorem operatorInformationNormReadout_le_of_weylThermodynamicComparison
    {residual central : EndH}
    (cmp : WeylThermodynamicOperatorComparison (E := E) residual central) :
    cmp.operatorInformationNormReadout residual ≤ cmp.operatorInformationNormReadout central := by
  rw [cmp.residual_readout_eq_relativeInformationNorm,
    cmp.central_readout_eq_relativeInformationNorm]
  exact cmp.relativeInformationNorm_le_central

/--
Profile-level Weyl/thermodynamic comparison packet for a scaled `L¹`
modular-potential residual readout bounded by a central thermodynamic readout.

This is the source-faithful packet for Sinkhorn RN barriers. It does not use
the RMS `relativeInformationNorm`; it uses the projective
`informationGeometricRelativeNorm` lane with explicit scale factors, because
raw RN barriers are sums of absolute logarithmic count/profile changes. The
central `Z_D` side remains an explicitly supplied thermodynamic scalar budget
until a separate central positive-ray profile is constructed.
-/
@[rep_depth transport]
structure WeylThermodynamicProfileComparison
    (residual central : EndH) where
  α : Type
  fintype : Fintype α
  nonempty : Nonempty α
  operatorInformationNormReadout : EndH → ℝ
  defectScale : ℝ
  defectScale_nonneg : 0 ≤ defectScale
  defectRay : InfoGeometry.Canonical.PositiveRayCore.PositiveRay α
  referenceRay : InfoGeometry.Canonical.PositiveRayCore.PositiveRay α
  residual_readout_eq_scaled_informationGeometricRelativeNorm :
    operatorInformationNormReadout residual =
      defectScale *
        @InfoGeometry.Canonical.RelativePotentialCore.informationGeometricRelativeNorm
          α fintype nonempty defectRay referenceRay
  scaled_informationGeometricRelativeNorm_le_central_readout :
    defectScale *
        @InfoGeometry.Canonical.RelativePotentialCore.informationGeometricRelativeNorm
          α fintype nonempty defectRay referenceRay
      ≤
    operatorInformationNormReadout central

omit [CompleteSpace E] in
/--
Readout-level consequence of a profile Weyl/thermodynamic comparison packet.
-/
@[rep_depth transport]
theorem operatorInformationNormReadout_le_of_weylThermodynamicProfileComparison
    {residual central : EndH}
    (cmp : WeylThermodynamicProfileComparison (E := E) residual central) :
    cmp.operatorInformationNormReadout residual ≤ cmp.operatorInformationNormReadout central := by
  rw [cmp.residual_readout_eq_scaled_informationGeometricRelativeNorm]
  exact cmp.scaled_informationGeometricRelativeNorm_le_central_readout

/--
Correct D3 closure target in the Weyl/thermodynamic language.

The observer defect is controlled by `Z_D` only after both operators have been
represented by the same normalized relative-measurement potential lane. This is
the operational comparison structure: Weyl gauge normalization, relative
measurement, and modular potential as negative logarithmic Radon-Nikodym
derivative.
-/
@[rep_depth transport]
def ObserverDefectResidualWeylThermodynamicBoundedByZD
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) : Prop :=
  -- DEBT_ID: LLM-ZD-001
  -- DEBT_KIND: ZERO_DATUM
  -- ZERO_DATUM: boundedness is recorded as a nonempty comparison property rather than a proven theorem.
  Nonempty
    (WeylThermodynamicOperatorComparison (E := E)
      (observerDefectResidual CIK obs)
      (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK))

/--
Any concrete Weyl/thermodynamic comparison packet closes the corrected D3
target. The proof is deliberately just packet transport: the real work is the
construction of the shared relative-potential representation.
-/
@[rep_depth transport]
theorem observerDefectResidualWeylThermodynamicBoundedByZD_of_comparison
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (cmp :
      WeylThermodynamicOperatorComparison (E := E)
        (observerDefectResidual CIK obs)
        (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK)) :
    ObserverDefectResidualWeylThermodynamicBoundedByZD (E := E) CIK obs :=
  ⟨cmp⟩

/--
Constructive property packet for the corrected Weyl/thermodynamic observer-defect
bound. This carries the comparison packet as explicit data, so downstream
constructors do not need to consume a bare `Nonempty` proposition when an
honest property is already available.
-/
@[rep_depth transport]
structure ObserverDefectResidualWeylThermodynamicControl
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK) where
  comparison :
    WeylThermodynamicOperatorComparison (E := E)
      (observerDefectResidual CIK obs)
      (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK)

/--
An explicit Weyl/thermodynamic control property closes the theorem-level bounded
observer-defect target.
-/
@[rep_depth transport]
theorem ObserverDefectResidualWeylThermodynamicBoundedByZD_of_control
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (c : ObserverDefectResidualWeylThermodynamicControl (E := E) CIK obs) :
    ObserverDefectResidualWeylThermodynamicBoundedByZD (E := E) CIK obs :=
  ⟨c.comparison⟩

/--
Thermodynamic router bridge.

This is the corrected D3 bridge surface: the router residual is identified with
the canonical observer defect and compared to `Z_D` through a shared
Weyl/thermodynamic relative-measurement readout. The legacy
`RouterDefectBoundBridge` below remains only for existing norm-shaped consumers.
-/
@[rep_depth transport]
structure RouterDefectThermodynamicBridge where
  CIK : CertifiedInverseKernel H₂
  obs : ObserverL5 CIK
  flow : BackgroundModularFlow CIK
  routerResidual : EndH
  residual_eq_observerDefect :
    routerResidual = observerDefectResidual CIK obs
  comparison :
    WeylThermodynamicOperatorComparison (E := E)
      routerResidual
      (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK)

namespace RouterDefectThermodynamicBridge

/--
Canonical constructor for the thermodynamic router bridge.

The residual is fixed to the canonical observer defect. The only remaining
input is the concrete Weyl/thermodynamic comparison packet, not an ambient
operator-norm bound.
-/
noncomputable def ofCanonicalObserverDefect
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (cmp :
      WeylThermodynamicOperatorComparison (E := E)
        (observerDefectResidual CIK obs)
        (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK)) :
    RouterDefectThermodynamicBridge (E := E) :=
  { CIK := CIK
    obs := obs
    flow := flow
    routerResidual := observerDefectResidual CIK obs
    residual_eq_observerDefect := rfl
    comparison := cmp }

@[simp] theorem ofCanonicalObserverDefect_routerResidual
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (cmp :
      WeylThermodynamicOperatorComparison (E := E)
        (observerDefectResidual CIK obs)
        (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK)) :
    (ofCanonicalObserverDefect (E := E) CIK obs flow cmp).routerResidual =
      observerDefectResidual CIK obs := by
  rfl

/-- Sourced generator built from the thermodynamic router residual. -/
noncomputable def sourcedGenerator (B : RouterDefectThermodynamicBridge (E := E)) : EndH :=
  B.flow.K0 + B.routerResidual

/-- The thermodynamic sourced generator coincides with the canonical sourced modular generator. -/
@[rep_depth transport]
theorem sourcedGenerator_eq_canonical
    (B : RouterDefectThermodynamicBridge (E := E)) :
    B.sourcedGenerator = sourcedModularGenerator B.CIK B.obs B.flow := by
  unfold sourcedGenerator sourcedModularGenerator
  simp [B.residual_eq_observerDefect]

/--
Thermodynamic residual comparison: the residual readout is bounded by the `Z_D`
readout in the shared Weyl/relative-potential representation.
-/
@[rep_depth transport]
theorem operatorInformationNormReadout_routerResidual_le_ZD
    (B : RouterDefectThermodynamicBridge (E := E)) :
    B.comparison.operatorInformationNormReadout B.routerResidual
      ≤
    B.comparison.operatorInformationNormReadout
      (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) B.CIK) :=
  operatorInformationNormReadout_le_of_weylThermodynamicComparison
    (E := E) B.comparison

/--
The thermodynamic bridge closes the corrected observer-defect target after
transporting the residual equality.
-/
@[rep_depth transport]
theorem observerDefectResidualWeylThermodynamicBoundedByZD
    (B : RouterDefectThermodynamicBridge (E := E)) :
    ObserverDefectResidualWeylThermodynamicBoundedByZD (E := E) B.CIK B.obs := by
  rcases B with ⟨CIK, obs, flow, routerResidual, hEq, comparison⟩
  dsimp [ObserverDefectResidualWeylThermodynamicBoundedByZD] at *
  subst routerResidual
  exact ⟨comparison⟩

/--
Canonical constructor for the thermodynamic router bridge from an explicit
Weyl/thermodynamic comparison property packet.

This keeps the corrected D3 transport on the theorem-backed constructor lane
without requiring downstream callers to eliminate the theorem-level `Nonempty`
packet themselves.
-/
noncomputable def ofWeylThermodynamicControl
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (c : ObserverDefectResidualWeylThermodynamicControl (E := E) CIK obs) :
    RouterDefectThermodynamicBridge (E := E) :=
  ofCanonicalObserverDefect (E := E) CIK obs flow c.comparison

@[simp] theorem ofWeylThermodynamicControl_routerResidual
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (c : ObserverDefectResidualWeylThermodynamicControl (E := E) CIK obs) :
    (ofWeylThermodynamicControl (E := E) CIK obs flow c).routerResidual =
      observerDefectResidual CIK obs := by
  simp [ofWeylThermodynamicControl]

/--
Canonical constructor for the thermodynamic router bridge from the theorem-level
Weyl/thermodynamic boundedness target.

This consumes the owner proposition `ObserverDefectResidualWeylThermodynamicBoundedByZD`
instead of requiring downstream callers to manually unpack a comparison packet.
-/
noncomputable def ofWeylThermodynamicBoundedByZD
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hBound : ObserverDefectResidualWeylThermodynamicBoundedByZD (E := E) CIK obs) :
    RouterDefectThermodynamicBridge (E := E) :=
  ofCanonicalObserverDefect (E := E) CIK obs flow (Classical.choice hBound)

@[simp] theorem ofWeylThermodynamicBoundedByZD_routerResidual
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hBound : ObserverDefectResidualWeylThermodynamicBoundedByZD (E := E) CIK obs) :
    (ofWeylThermodynamicBoundedByZD (E := E) CIK obs flow hBound).routerResidual =
      observerDefectResidual CIK obs := by
  simp [ofWeylThermodynamicBoundedByZD]

end RouterDefectThermodynamicBridge

/--
Canonical theorem-backed constructor for the bounded bridge.

This constructor identifies the router residual with the canonical observer-defect
residual. The bound is derived from the deviation-control predicate instead of
requiring an explicit norm-bound property.
-/
noncomputable def ofCanonicalObserverDefect
  (CIK : CertifiedInverseKernel H₂)
  (obs : ObserverL5 CIK)
  (flow : BackgroundModularFlow CIK)
  (hControl : ObserverDeviationControlledByZD CIK obs) :
  RouterDefectBoundBridge (E := E) :=
  { CIK := CIK
    flow := flow
    routerResidual := observerDefectResidual CIK obs
    residual_norm_le_ZD := observerDefectResidual_norm_le_ZD CIK obs hControl }

/--
Core canonical constructor for a canonical observer controlled by `Z_D` — this route
consumes the owner predicate `ObserverDeviationControlledByZD` directly, eliminating
the explicit bound property on this lane.
-/
noncomputable def ofCanonicalControlledObserver
  (CIK : CertifiedInverseKernel H₂)
  (obs : ObserverL5 CIK)
  (flow : BackgroundModularFlow CIK)
  (hControl : ObserverDeviationControlledByZD CIK obs) :
  RouterDefectBoundBridge (E := E) :=
  { CIK := CIK
    flow := flow
    routerResidual := observerDefectResidual CIK obs
    residual_norm_le_ZD := observerDefectResidual_norm_le_ZD (E := E) CIK obs hControl }

/--
Constructive bounded constructor for a canonical observer whose exact deviation
commutator channel is controlled by `Z_D` on the owner lane.
-/
noncomputable def ofZDControlledObserver
  (CIK : CertifiedInverseKernel H₂)
  (obs : ObserverL5 CIK)
  (flow : BackgroundModularFlow CIK)
  (hControl : ObserverDeviationControlledByZD CIK obs) :
  RouterDefectBoundBridge (E := E) :=
  ofCanonicalControlledObserver CIK obs flow hControl

/--
Constructive bounded constructor for a canonical observer carrying an explicit
owner-side deviation-control property packet.
-/
noncomputable def ofControlObserver
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (c : ObserverDeviationControl CIK obs) :
    RouterDefectBoundBridge (E := E) :=
  ofZDControlledObserver (E := E) CIK obs flow
    (ObserverDeviationControlledByZD.of_control c)

/--
Constructive bounded constructor for an observer whose compressed deviation
commutator channel is already zero on the defect block.
-/
noncomputable def ofCompressedDeviationZeroObserver
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hZero :
      CIK.spectralComplementaryProjector *
        DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap *
        CIK.spectralComplementaryProjector = 0) :
    RouterDefectBoundBridge (E := E) :=
  ofCanonicalObserverDefect (E := E) CIK obs flow
    (observerDeviationControlledByZD_of_compressedDeviation_eq_zero
      (CIK := CIK) (obs := obs) hZero)

@[simp] theorem ofCompressedDeviationZeroObserver_routerResidual
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hZero :
      CIK.spectralComplementaryProjector *
        DrazinSupercharge.commutator (observerProjectorDeviation CIK obs) CIK.dilationGap *
        CIK.spectralComplementaryProjector = 0) :
    (ofCompressedDeviationZeroObserver (E := E) CIK obs flow hZero).routerResidual = 0 := by
  have hResidual : observerDefectResidual CIK obs = 0 :=
    observerDefectResidual_eq_zero_of_compressedDeviation_eq_zero (CIK := CIK) (obs := obs) hZero
  simpa [ofCompressedDeviationZeroObserver, ofCanonicalObserverDefect] using hResidual

/--
If the operatorial defect-central/Casimir channel `Z_D` is zero, then the
`Z_D`-controlled router residual produced from the canonical observer lane is
zero.
-/
@[simp] theorem ofZDControlledObserver_routerResidual_eq_zero_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hControl : ObserverDeviationControlledByZD CIK obs)
    (hZD :
      InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    (ofZDControlledObserver (E := E) CIK obs flow hControl).routerResidual = 0 := by
  have hResidual :
      observerDefectResidual CIK obs = 0 :=
    observerDefectResidual_eq_zero_of_deviationControlledByZD_of_ZD_eq_zero
      (E := E) (CIK := CIK) (obs := obs) hControl hZD
  simpa [ofZDControlledObserver] using hResidual

@[simp] theorem ofControlObserver_routerResidual_eq_zero_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (c : ObserverDeviationControl CIK obs)
    (hZD :
      InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    (ofControlObserver (E := E) CIK obs flow c).routerResidual = 0 := by
  simpa [ofControlObserver] using
    ofZDControlledObserver_routerResidual_eq_zero_of_ZD_eq_zero
      (E := E) (CIK := CIK) (obs := obs) (flow := flow)
      (hControl := ObserverDeviationControlledByZD.of_control c)
      (hZD := hZD)

@[simp] theorem ofCanonicalObserverDefect_routerResidual
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hControl : ObserverDeviationControlledByZD CIK obs) :
    (ofCanonicalObserverDefect (E := E) CIK obs flow hControl).routerResidual = observerDefectResidual CIK obs := by
  rfl

/--
Zero-defect bounded constructor for an aligned observer.

This closes the `ZD` budget without a free inequality property in the
equilibrium lane: alignment constructs an explicit owner-side
`ObserverDeviationControl` property, and the general `ofControlObserver`
constructor consumes that packet without reopening a bridge-local residual
budget.
-/
noncomputable def ofAlignedObserver
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hAlign : observerOrientationResidual CIK obs = 0) :
    RouterDefectBoundBridge (E := E) :=
  ofControlObserver (E := E) CIK obs flow
    (observerDeviationControl_of_aligned
      (E := E) (CIK := CIK) (obs := obs) hAlign)

/--
Zero-defect bounded constructor for an observer whose scalarized orientation
strain already vanishes on the owner lane.
-/
noncomputable def ofStrainZeroObserver
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hStrain : observerOrientationStrain CIK obs = 0) :
    RouterDefectBoundBridge (E := E) :=
  ofCanonicalObserverDefect (E := E) CIK obs flow
    (observerDeviationControlledByZD_of_strain_eq_zero
      (CIK := CIK) (obs := obs) hStrain)

/--
Zero-defect bounded constructor for an observer whose local slice is exactly the
property spectral projector.  The owner lane first constructs the exact
deviation-control predicate, and the bounded bridge is then obtained from the
general `ofZDControlledObserver` constructor.
-/
noncomputable def ofDeviationZeroObserver
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hDev : observerProjectorDeviation CIK obs = 0) :
    RouterDefectBoundBridge (E := E) :=
  ofZDControlledObserver (E := E) CIK obs flow
    (observerDeviationControlledByZD_of_deviation_eq_zero
      (E := E) (CIK := CIK) (obs := obs) hDev)

@[simp] theorem ofDeviationZeroObserver_routerResidual
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hDev : observerProjectorDeviation CIK obs = 0) :
    (ofDeviationZeroObserver (E := E) CIK obs flow hDev).routerResidual = 0 := by
  have _hControl : ObserverDeviationControlledByZD CIK obs :=
    observerDeviationControlledByZD_of_deviation_eq_zero (CIK := CIK) (obs := obs) hDev
  have hResidual : observerDefectResidual CIK obs = 0 :=
    observerDefectResidual_eq_zero_of_deviation_eq_zero (CIK := CIK) (obs := obs) hDev
  simpa [ofDeviationZeroObserver, ofZDControlledObserver, ofCanonicalObserverDefect] using hResidual

@[simp] theorem ofStrainZeroObserver_routerResidual
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hStrain : observerOrientationStrain CIK obs = 0) :
    (ofStrainZeroObserver (E := E) CIK obs flow hStrain).routerResidual = 0 := by
  have _hControl : ObserverDeviationControlledByZD CIK obs :=
    observerDeviationControlledByZD_of_strain_eq_zero (CIK := CIK) (obs := obs) hStrain
  have hResidual : observerDefectResidual CIK obs = 0 :=
    observerDefectResidual_eq_zero_of_strain_eq_zero (CIK := CIK) (obs := obs) hStrain
  simpa [ofStrainZeroObserver, ofZDControlledObserver, ofCanonicalObserverDefect] using hResidual

@[simp] theorem ofAlignedObserver_routerResidual
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hAlign : observerOrientationResidual CIK obs = 0) :
    (ofAlignedObserver (E := E) CIK obs flow hAlign).routerResidual = 0 := by
  have hResidual : observerDefectResidual CIK obs = 0 :=
    observerDefectResidual_eq_zero_of_aligned (CIK := CIK) (obs := obs) hAlign
  simpa [ofAlignedObserver, ofZDControlledObserver, ofCanonicalObserverDefect] using hResidual

/-- Sourced generator built from the bounded LLM-side residual input. -/
noncomputable def sourcedGenerator (B : RouterDefectBoundBridge (E := E)) : EndH :=
  B.flow.K0 + B.routerResidual

/--
The bounded sourced generator equals the background flow exactly when the router
residual vanishes.
-/
theorem sourcedGenerator_eq_flow_iff_routerResidual_eq_zero
    (B : RouterDefectBoundBridge (E := E)) :
    B.sourcedGenerator = B.flow.K0 ↔ B.routerResidual = 0 := by
  constructor
  · intro h
    have hSub := congrArg (fun T => T - B.flow.K0) h
    unfold RouterDefectBoundBridge.sourcedGenerator at hSub
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hSub
  · intro hResidual
    unfold RouterDefectBoundBridge.sourcedGenerator
    simpa [hResidual]

/--
If the exact deviation channel is controlled by `Z_D` and `Z_D` itself vanishes,
then the bounded router sourced generator collapses to the background flow.
-/
@[rep_depth transport]
theorem ofZDControlledObserver_sourcedGenerator_eq_flow_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hControl : ObserverDeviationControlledByZD CIK obs)
    (hZD :
      InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    (ofZDControlledObserver (E := E) CIK obs flow hControl).sourcedGenerator = flow.K0 := by
  rw [RouterDefectBoundBridge.sourcedGenerator]
  rw [ofZDControlledObserver_routerResidual_eq_zero_of_ZD_eq_zero
    (E := E) (CIK := CIK) (obs := obs) (flow := flow) (hControl := hControl) (hZD := hZD)]
  simp [ofZDControlledObserver, ofCanonicalControlledObserver]

/--
If the exact deviation channel is controlled by `Z_D` and `Z_D` itself vanishes,
then Drazin-cut preservation reduces to the background-flow commutation theorem.
-/
@[rep_depth transport]
theorem ofZDControlledObserver_sourcedGenerator_respects_cut_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hControl : ObserverDeviationControlledByZD CIK obs)
    (hZD :
      InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    Commute
      (ofZDControlledObserver (E := E) CIK obs flow hControl).sourcedGenerator
      CIK.spectralComplementaryProjector := by
  rw [ofZDControlledObserver_sourcedGenerator_eq_flow_of_ZD_eq_zero
    (E := E) CIK obs flow hControl hZD]
  exact flow.commutesQ0

/--
If an observer is carried by an explicit owner-side deviation-control property and
`Z_D` vanishes, the bounded sourced generator collapses to the background flow.
-/
@[rep_depth transport]
theorem ofControlObserver_sourcedGenerator_eq_flow_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (c : ObserverDeviationControl CIK obs)
    (hZD :
      InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    (ofControlObserver (E := E) CIK obs flow c).sourcedGenerator = flow.K0 := by
  simpa [ofControlObserver] using
    ofZDControlledObserver_sourcedGenerator_eq_flow_of_ZD_eq_zero
      (E := E) (CIK := CIK) (obs := obs) (flow := flow)
      (hControl := ObserverDeviationControlledByZD.of_control c)
      (hZD := hZD)

/--
If an observer is carried by an explicit owner-side deviation-control property and
`Z_D` vanishes, Drazin-cut preservation reduces to flow commutation.
-/
@[rep_depth transport]
theorem ofControlObserver_sourcedGenerator_respects_cut_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (c : ObserverDeviationControl CIK obs)
    (hZD :
      InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    Commute
      (ofControlObserver (E := E) CIK obs flow c).sourcedGenerator
      CIK.spectralComplementaryProjector := by
  rw [ofControlObserver_sourcedGenerator_eq_flow_of_ZD_eq_zero
    (E := E) CIK obs flow c hZD]
  exact flow.commutesQ0

/--
Strain-zero sourced-flow collapse for the control-property constructor.

This is a constructive infinite-lane descent that removes the extra `Z_D = 0`
input on this branch: the owner theorem
`observerDefectResidual_eq_zero_of_strain_eq_zero` already discharges residual
vanishing from strain zero.
-/
@[rep_depth transport]
theorem ofControlObserver_sourcedGenerator_eq_flow_of_strain_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (c : ObserverDeviationControl CIK obs)
    (hStrain : observerOrientationStrain CIK obs = 0) :
    (ofControlObserver (E := E) CIK obs flow c).sourcedGenerator = flow.K0 := by
  refine
    (sourcedGenerator_eq_flow_iff_routerResidual_eq_zero
      (B := ofControlObserver (E := E) CIK obs flow c)).2 ?_
  have hResidual : observerDefectResidual CIK obs = 0 :=
    observerDefectResidual_eq_zero_of_strain_eq_zero
      (CIK := CIK) (obs := obs) hStrain
  simpa [ofControlObserver, ofZDControlledObserver, ofCanonicalObserverDefect] using hResidual

/--
On the exact projector-deviation-zero branch, the control-property constructor
already collapses the router residual without any extra `Z_D = 0` property.
-/
@[rep_depth transport]
theorem ofControlObserver_routerResidual_eq_zero_of_deviation_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (c : ObserverDeviationControl CIK obs)
    (hDev : observerProjectorDeviation CIK obs = 0) :
    (ofControlObserver (E := E) CIK obs flow c).routerResidual = 0 := by
  have hResidual : observerDefectResidual CIK obs = 0 :=
    observerDefectResidual_eq_zero_of_deviation_eq_zero
      (CIK := CIK) (obs := obs) hDev
  simpa [ofControlObserver, ofZDControlledObserver, ofCanonicalObserverDefect] using hResidual

/--
On the exact projector-deviation-zero branch, the control-property constructor
already collapses the sourced generator to the background flow without any extra
`Z_D = 0` property.
-/
@[rep_depth transport]
theorem ofControlObserver_sourcedGenerator_eq_flow_of_deviation_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (c : ObserverDeviationControl CIK obs)
    (hDev : observerProjectorDeviation CIK obs = 0) :
    (ofControlObserver (E := E) CIK obs flow c).sourcedGenerator = flow.K0 := by
  exact
    (sourcedGenerator_eq_flow_iff_routerResidual_eq_zero
      (B := ofControlObserver (E := E) CIK obs flow c)).2
      (ofControlObserver_routerResidual_eq_zero_of_deviation_eq_zero
        (E := E) (CIK := CIK) (obs := obs) (flow := flow) (c := c) (hDev := hDev))

/--
Under zero central defect, the control-property constructor forces zero scalarized
observer strain on the owner lane.
-/
@[rep_depth transport]
theorem ofControlObserver_observerOrientationStrain_eq_zero_of_ZD_eq_zero
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (c : ObserverDeviationControl CIK obs)
    (hZD :
      InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK = 0) :
    observerOrientationStrain CIK obs = 0 := by
  exact observerOrientationStrain_eq_zero_of_control_of_ZD_eq_zero
    (CIK := CIK) (obs := obs) hZD c

/--
For a deviation-zero observer, the bounded router sourced generator collapses to
the background flow generator.
-/
@[rep_depth transport]
theorem ofDeviationZeroObserver_sourcedGenerator_eq_flow
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hDev : observerProjectorDeviation CIK obs = 0) :
    (ofDeviationZeroObserver (E := E) CIK obs flow hDev).sourcedGenerator = flow.K0 := by
  rw [RouterDefectBoundBridge.sourcedGenerator]
  rw [ofDeviationZeroObserver_routerResidual (E := E) (CIK := CIK) (obs := obs)
    (flow := flow) (hDev := hDev)]
  simp [ofDeviationZeroObserver, ofZDControlledObserver, ofCanonicalControlledObserver]

/--
For a deviation-zero observer, Drazin-cut preservation reduces to the
background-flow commutation theorem.
-/
@[rep_depth transport]
theorem ofDeviationZeroObserver_sourcedGenerator_respects_cut
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hDev : observerProjectorDeviation CIK obs = 0) :
    Commute
      (ofDeviationZeroObserver (E := E) CIK obs flow hDev).sourcedGenerator
      CIK.spectralComplementaryProjector := by
  rw [ofDeviationZeroObserver_sourcedGenerator_eq_flow (E := E) CIK obs flow hDev]
  exact flow.commutesQ0

/--
For an aligned observer, the bounded router sourced generator collapses to the
background flow generator.
-/
@[rep_depth transport]
theorem ofAlignedObserver_sourcedGenerator_eq_flow
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hAlign : observerOrientationResidual CIK obs = 0) :
    (ofAlignedObserver (E := E) CIK obs flow hAlign).sourcedGenerator = flow.K0 := by
  exact
    (sourcedGenerator_eq_flow_iff_routerResidual_eq_zero
      (B := ofAlignedObserver (E := E) CIK obs flow hAlign)).2
      (ofAlignedObserver_routerResidual (E := E) (CIK := CIK) (obs := obs)
        (flow := flow) (hAlign := hAlign))

/--
For an aligned observer, Drazin-cut preservation reduces to the background-flow
commutation theorem.
-/
@[rep_depth transport]
theorem ofAlignedObserver_sourcedGenerator_respects_cut
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hAlign : observerOrientationResidual CIK obs = 0) :
    Commute
      (ofAlignedObserver (E := E) CIK obs flow hAlign).sourcedGenerator
      CIK.spectralComplementaryProjector := by
  rw [ofAlignedObserver_sourcedGenerator_eq_flow (E := E) CIK obs flow hAlign]
  exact flow.commutesQ0

/--
For a strain-zero observer, the bounded router sourced generator collapses to the
background flow generator.
-/
@[rep_depth transport]
theorem ofStrainZeroObserver_sourcedGenerator_eq_flow
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hStrain : observerOrientationStrain CIK obs = 0) :
    (ofStrainZeroObserver (E := E) CIK obs flow hStrain).sourcedGenerator = flow.K0 := by
  exact
    (sourcedGenerator_eq_flow_iff_routerResidual_eq_zero
      (B := ofStrainZeroObserver (E := E) CIK obs flow hStrain)).2
      (ofStrainZeroObserver_routerResidual (E := E) (CIK := CIK) (obs := obs)
        (flow := flow) (hStrain := hStrain))

/--
For a strain-zero observer, Drazin-cut preservation reduces to the
background-flow commutation theorem.
-/
@[rep_depth transport]
theorem ofStrainZeroObserver_sourcedGenerator_respects_cut
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hStrain : observerOrientationStrain CIK obs = 0) :
    Commute
      (ofStrainZeroObserver (E := E) CIK obs flow hStrain).sourcedGenerator
      CIK.spectralComplementaryProjector := by
  rw [ofStrainZeroObserver_sourcedGenerator_eq_flow (E := E) CIK obs flow hStrain]
  exact flow.commutesQ0

/--
For the canonical bounded constructor, the LLM-side sourced generator is the
canonical sourced modular generator.
-/
@[rep_depth transport]
theorem ofCanonicalObserverDefect_sourcedGenerator_eq_canonical
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hControl : ObserverDeviationControlledByZD CIK obs) :
    (ofCanonicalObserverDefect (E := E) CIK obs flow hControl).sourcedGenerator =
      sourcedModularGenerator CIK obs flow := by
  rfl

/--
The canonical bounded constructor inherits Drazin-cut preservation from the
canonical sourced modular generator.
-/
@[rep_depth transport]
theorem ofCanonicalObserverDefect_sourcedGenerator_respects_cut
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hControl : ObserverDeviationControlledByZD CIK obs) :
    Commute
      (ofCanonicalObserverDefect (E := E) CIK obs flow hControl).sourcedGenerator
      CIK.spectralComplementaryProjector := by
  rw [ofCanonicalObserverDefect_sourcedGenerator_eq_canonical
    (E := E) CIK obs flow hControl]
  exact sourcedModularGenerator_respects_spectral_cut (CIK := CIK) (obs := obs) (flow := flow)

/-- The residual budget is exactly the sourced-generator deviation from baseline flow. -/
@[rep_depth transport]
theorem sourcedGenerator_deviation_norm_le_ZD
  (B : RouterDefectBoundBridge (E := E)) :
  ‖B.sourcedGenerator - B.flow.K0‖ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) B.CIK‖ := by
  simpa [sourcedGenerator, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
  B.residual_norm_le_ZD

/--
Constructive readback for the property-routed bounded constructor: the router residual
inherits the canonical `Z_D` budget from the explicit `ObserverDeviationControl`
packet, without reopening a bare `ObserverDeviationControlledByZD` property.
-/
@[rep_depth transport]
theorem ofControlObserver_routerResidual_norm_le_ZD
  (CIK : CertifiedInverseKernel H₂)
  (obs : ObserverL5 CIK)
  (flow : BackgroundModularFlow CIK)
  (c : ObserverDeviationControl CIK obs) :
  ‖(ofControlObserver (E := E) CIK obs flow c).routerResidual‖ ≤
    ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖ := by
  exact (ofControlObserver (E := E) CIK obs flow c).residual_norm_le_ZD

/--
Compatibility readback for the predicate-routed bounded constructor: the router residual
inherits the canonical `Z_D` budget directly from the constructor record.
-/
@[rep_depth transport]
theorem ofZDControlledObserver_routerResidual_norm_le_ZD
  (CIK : CertifiedInverseKernel H₂)
  (obs : ObserverL5 CIK)
  (flow : BackgroundModularFlow CIK)
  (hControl : ObserverDeviationControlledByZD CIK obs) :
  ‖(ofZDControlledObserver (E := E) CIK obs flow hControl).routerResidual‖ ≤
    ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖ := by
  exact (ofZDControlledObserver (E := E) CIK obs flow hControl).residual_norm_le_ZD

end RouterDefectBoundBridge

end CanonicalBridge

end InfoGeometry.LLM.TrialityMoE

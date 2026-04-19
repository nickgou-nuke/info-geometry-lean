import InfoGeometry.Canonical.ObserverDefect
import InfoGeometry.Canonical.ModularSourceBridge
import InfoGeometry.Canonical.KKTClosureSymmetry
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
Bridge assumption linking an LLM router-residual operator to the canonical observer-defect residual.
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
@[rep_depth transport]
theorem sourcedGenerator_eq_canonical (B : RouterDefectBridge (E := E)) :
    B.sourcedGenerator = sourcedModularGenerator B.CIK B.obs B.flow := by
  unfold sourcedGenerator sourcedModularGenerator
  simp [B.residual_eq_observerDefect]

/-- Drazin-cut preservation follows immediately once the router residual is identified canonically. -/
@[rep_depth transport]
theorem sourcedGenerator_respects_cut (B : RouterDefectBridge (E := E)) :
    Commute B.sourcedGenerator B.CIK.spectralComplementaryProjector := by
  rw [sourcedGenerator_eq_canonical (B := B)]
  exact sourcedModularGenerator_respects_spectral_cut (CIK := B.CIK) (obs := B.obs) (flow := B.flow)

end RouterDefectBridge

/--
Bounded bridge variant: the router residual is controlled by the canonical
defect-central channel `Z_D` on the same Drazin/KKT lane.
-/
structure RouterDefectBoundBridge where
  CIK : CertifiedInverseKernel H₂
  flow : BackgroundModularFlow CIK
  routerResidual : EndH
  residual_norm_le_ZD :
    ‖routerResidual‖ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖

namespace RouterDefectBoundBridge

/--
Canonical theorem-backed constructor for the bounded bridge.

This constructor identifies the router residual with the canonical observer-defect
residual. The bound proof remains explicit until a general canonical inequality
linking `observerDefectResidual` to `Z_D` is established upstream.
-/
noncomputable def ofCanonicalObserverDefect
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hBound : ‖observerDefectResidual CIK obs‖ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖) :
    RouterDefectBoundBridge (E := E) :=
  { CIK := CIK
    flow := flow
    routerResidual := observerDefectResidual CIK obs
    residual_norm_le_ZD := hBound }

@[simp] theorem ofCanonicalObserverDefect_routerResidual
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hBound : ‖observerDefectResidual CIK obs‖ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖) :
    (ofCanonicalObserverDefect (E := E) CIK obs flow hBound).routerResidual = observerDefectResidual CIK obs := by
  rfl

/--
Zero-defect bounded constructor for an aligned observer.

This closes the `ZD` budget without a free inequality assumption in the
equilibrium lane: alignment forces the canonical observer defect to vanish, and
`0 ≤ ‖Z_D‖` supplies the bound.
-/
noncomputable def ofAlignedObserver
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hAlign : observerOrientationResidual CIK obs = 0) :
    RouterDefectBoundBridge (E := E) :=
  ofCanonicalObserverDefect (E := E) CIK obs flow (by
    have hZero : observerDefectResidual CIK obs = 0 :=
      observerDefectResidual_eq_zero_of_aligned (CIK := CIK) (obs := obs) hAlign
    rw [hZero]
    calc
      ‖(0 : EndH)‖ = 0 := ContinuousLinearMap.opNorm_zero
      _ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖ :=
        norm_nonneg (InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK))

@[simp] theorem ofAlignedObserver_routerResidual
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hAlign : observerOrientationResidual CIK obs = 0) :
    (ofAlignedObserver (E := E) CIK obs flow hAlign).routerResidual = 0 := by
  have hZero : observerDefectResidual CIK obs = 0 :=
    observerDefectResidual_eq_zero_of_aligned (CIK := CIK) (obs := obs) hAlign
  simpa [ofAlignedObserver] using hZero

/-- Sourced generator built from the bounded LLM-side residual input. -/
noncomputable def sourcedGenerator (B : RouterDefectBoundBridge (E := E)) : EndH :=
  B.flow.K0 + B.routerResidual

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
  have hZero : observerDefectResidual CIK obs = 0 :=
    observerDefectResidual_eq_zero_of_aligned (CIK := CIK) (obs := obs) hAlign
  simp [RouterDefectBoundBridge.sourcedGenerator, ofAlignedObserver,
    ofCanonicalObserverDefect, hZero]

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
For the canonical bounded constructor, the LLM-side sourced generator is the
canonical sourced modular generator.
-/
@[rep_depth transport]
theorem ofCanonicalObserverDefect_sourcedGenerator_eq_canonical
    (CIK : CertifiedInverseKernel H₂)
    (obs : ObserverL5 CIK)
    (flow : BackgroundModularFlow CIK)
    (hBound : ‖observerDefectResidual CIK obs‖ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖) :
    (ofCanonicalObserverDefect (E := E) CIK obs flow hBound).sourcedGenerator =
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
    (hBound : ‖observerDefectResidual CIK obs‖ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) CIK‖) :
    Commute
      (ofCanonicalObserverDefect (E := E) CIK obs flow hBound).sourcedGenerator
      CIK.spectralComplementaryProjector := by
  rw [ofCanonicalObserverDefect_sourcedGenerator_eq_canonical
    (E := E) CIK obs flow hBound]
  exact sourcedModularGenerator_respects_spectral_cut (CIK := CIK) (obs := obs) (flow := flow)

/-- The residual budget is exactly the sourced-generator deviation from baseline flow. -/
@[rep_depth transport]
theorem sourcedGenerator_deviation_norm_le_ZD
    (B : RouterDefectBoundBridge (E := E)) :
    ‖B.sourcedGenerator - B.flow.K0‖ ≤ ‖InfoGeometry.Canonical.KKTClosure.ZD (E := H₂) B.CIK‖ := by
  simpa [sourcedGenerator, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    B.residual_norm_le_ZD

end RouterDefectBoundBridge

end CanonicalBridge

end InfoGeometry.LLM.TrialityMoE

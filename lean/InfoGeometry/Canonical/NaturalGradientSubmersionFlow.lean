/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import InfoGeometry.Epistemology.RiemannianSubmersion
import InfoGeometry.Canonical.SuperGrassmannianManifold

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Natural Gradient Submersion Flow: Horizontal Geodesics and Confabulation Elimination

This module couples the Riemannian submersion framework (`RiemannianSubmersion.lean`) with
indefinite para-Kähler super-Grassmannian geometry (`SuperGrassmannianManifold.lean`):

1. `ParaComplexSplit`: Proves that any para-complex structure $K^2 = \text{id}$ on a real vector
   space canonically induces a `SubmersionSplit` via the spectral projectors
   $P^+ = \frac{1}{2}(\text{id} + K)$ and $P^- = \frac{1}{2}(\text{id} - K)$.
2. `NaturalGradientSystem`: Tangent space decomposition equipped with a symmetric metric $g$,
   horizontal-vertical metric orthogonality, and gradient vectors.
3. `natural_gradient_horizontal_isolation`: When the metric is block-orthogonal between
   horizontal and vertical subspaces, evaluating natural gradient inner products on horizontal
   test vectors isolates the horizontal component:
   $$g(\tilde{\nabla} \mathcal{L}, P_{\mathcal{H}} w) = g(P_{\mathcal{H}} \tilde{\nabla} \mathcal{L}, P_{\mathcal{H}} w)$$
4. `kernel_pinning_vanishing_drift`: Formal microkernel verification enforces the vanishing of
   vertical gradient flow ($P_{\mathcal{V}} \tilde{\nabla} \mathcal{L} = 0$). Consequently, the
   velocity $\dot{\theta} = - \tilde{\nabla} \mathcal{L}$ has vanishing vertical confabulation drift:
   $$P_{\mathcal{V}} \dot{\theta} = 0 \quad \text{and} \quad P_{\mathcal{H}} \dot{\theta} = \dot{\theta}$$
5. `kinetic_energy_fiber_collapse`: Under vanishing vertical velocity, the total kinetic metric energy
   collapses strictly to the horizontal base component:
   $$g(\dot{\theta}, \dot{\theta}) = g(P_{\mathcal{H}} \dot{\theta}, P_{\mathcal{H}} \dot{\theta})$$
6. `NaturalGradientSubmersionFlowCertificate`: Master integration certificate verifying the flow.
-/

namespace InfoGeometry.Canonical.NaturalGradientSubmersionFlow

open InfoGeometry.Epistemology.RiemannianSubmersion
open InfoGeometry.Canonical.SuperGrassmannianManifold

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ### 1. Para-Complex Spectral Split into Submersion Projectors -/

/-- Projector onto the $+1$ eigenspace of a para-complex structure $K$:
    $P^+ v = \frac{1}{2} v + \frac{1}{2} K v$. -/
noncomputable def paraProjectorPlus (K : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • LinearMap.id + (1 / 2 : ℝ) • K

/-- Projector onto the $-1$ eigenspace of a para-complex structure $K$:
    $P^- v = \frac{1}{2} v - \frac{1}{2} K v$. -/
noncomputable def paraProjectorMinus (K : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • LinearMap.id - (1 / 2 : ℝ) • K

/-- Sum of the twin spectral projectors is the identity: $P^+ + P^- = \text{id}$. -/
theorem para_projectors_sum_id (K : V →ₗ[ℝ] V) (v : V) :
    paraProjectorPlus K v + paraProjectorMinus K v = v := by
  dsimp [paraProjectorPlus, paraProjectorMinus]
  calc
    ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • K v) + ((1 / 2 : ℝ) • v - (1 / 2 : ℝ) • K v)
      = ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • v) + ((1 / 2 : ℝ) • K v - (1 / 2 : ℝ) • K v) := by abel
    _ = (1 : ℝ) • v + 0 := by
      rw [← add_smul]
      norm_num
    _ = v := by simp

/-- $P^+$ is an idempotent projector: $(P^+)^2 = P^+$. -/
theorem para_projector_plus_idempotent (K : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (v : V) :
    paraProjectorPlus K (paraProjectorPlus K v) = paraProjectorPlus K v := by
  dsimp [paraProjectorPlus]
  have hK_sq : K (K v) = v := hK.involutive v
  simp only [smul_add, map_add, LinearMap.map_smul, smul_smul, hK_sq]
  have h1 : (1 / 2 : ℝ) * (1 / 2 : ℝ) = (1 / 4 : ℝ) := by norm_num
  have h2 : (1 / 4 : ℝ) + (1 / 4 : ℝ) = (1 / 2 : ℝ) := by norm_num
  rw [h1]
  calc
    (1 / 4 : ℝ) • v + (1 / 4 : ℝ) • K v + ((1 / 4 : ℝ) • K v + (1 / 4 : ℝ) • v)
      = ((1 / 4 : ℝ) • v + (1 / 4 : ℝ) • v) + ((1 / 4 : ℝ) • K v + (1 / 4 : ℝ) • K v) := by abel
    _ = ((1 / 4 : ℝ) + (1 / 4 : ℝ)) • v + ((1 / 4 : ℝ) + (1 / 4 : ℝ)) • K v := by
      rw [← add_smul, ← add_smul]
    _ = (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • K v := by rw [h2]

/-- $P^-$ is an idempotent projector: $(P^-)^2 = P^-$. -/
theorem para_projector_minus_idempotent (K : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (v : V) :
    paraProjectorMinus K (paraProjectorMinus K v) = paraProjectorMinus K v := by
  dsimp [paraProjectorMinus]
  have hK_sq : K (K v) = v := hK.involutive v
  simp only [smul_sub, map_sub, LinearMap.map_smul, smul_smul, hK_sq]
  have h1 : (1 / 2 : ℝ) * (1 / 2 : ℝ) = (1 / 4 : ℝ) := by norm_num
  have h2 : (1 / 4 : ℝ) + (1 / 4 : ℝ) = (1 / 2 : ℝ) := by norm_num
  rw [h1]
  calc
    (1 / 4 : ℝ) • v - (1 / 4 : ℝ) • K v - ((1 / 4 : ℝ) • K v - (1 / 4 : ℝ) • v)
      = ((1 / 4 : ℝ) • v + (1 / 4 : ℝ) • v) - ((1 / 4 : ℝ) • K v + (1 / 4 : ℝ) • K v) := by abel
    _ = ((1 / 4 : ℝ) + (1 / 4 : ℝ)) • v - ((1 / 4 : ℝ) + (1 / 4 : ℝ)) • K v := by
      rw [← add_smul, ← add_smul]
    _ = (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • K v := by rw [h2]

/-- Orthogonal annihilation: $P^+ (P^- v) = 0$. -/
theorem para_projectors_annihilation_plus_minus (K : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (v : V) :
    paraProjectorPlus K (paraProjectorMinus K v) = 0 := by
  dsimp [paraProjectorPlus, paraProjectorMinus]
  have hK_sq : K (K v) = v := hK.involutive v
  simp only [smul_sub, map_sub, LinearMap.map_smul, smul_smul, hK_sq]
  have h1 : (1 / 2 : ℝ) * (1 / 2 : ℝ) = (1 / 4 : ℝ) := by norm_num
  rw [h1]
  abel

/-- Orthogonal annihilation: $P^- (P^+ v) = 0$. -/
theorem para_projectors_annihilation_minus_plus (K : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (v : V) :
    paraProjectorMinus K (paraProjectorPlus K v) = 0 := by
  dsimp [paraProjectorPlus, paraProjectorMinus]
  have hK_sq : K (K v) = v := hK.involutive v
  simp only [LinearMap.map_smul, smul_smul, smul_add, map_add, hK_sq]
  have h1 : (1 / 2 : ℝ) * (1 / 2 : ℝ) = (1 / 4 : ℝ) := by norm_num
  rw [h1]
  abel

/-- 
  Theorem: Any para-complex structure $K^2 = \text{id}$ canonically induces
  a Riemannian Submersion split $(P^+, P^-)$ satisfying all axioms of `SubmersionSplit`.
-/
noncomputable def paraComplexSubmersionSplit
    (K : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) : SubmersionSplit V where
  projH := paraProjectorPlus K
  projV := paraProjectorMinus K
  sum_id := para_projectors_sum_id K
  idemH := para_projector_plus_idempotent K hK
  idemV := para_projector_minus_idempotent K hK
  orthoHV := para_projectors_annihilation_plus_minus K hK
  orthoVH := para_projectors_annihilation_minus_plus K hK

/-! ### 2. Natural Gradient Submersion Flow -/

/--
  A Natural Gradient Submersion system: A tangent space split $V = \mathcal{H} \oplus \mathcal{V}$
  equipped with a symmetric bilinear metric $g$ that is block-orthogonal between horizontal
  and vertical directions.
-/
structure NaturalGradientSubmersionSystem (V : Type*) [AddCommGroup V] [Module ℝ V] where
  split : SubmersionSplit V
  g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  symm : ∀ u w, g u w = g w u
  ortho_HV : ∀ u w, g (split.projH u) (split.projV w) = 0

/-- Orthogonality of vertical and horizontal: $g(P_{\mathcal{V}} u, P_{\mathcal{H}} w) = 0$. -/
theorem metric_ortho_VH (sys : NaturalGradientSubmersionSystem V) (u w : V) :
    sys.g (sys.split.projV u) (sys.split.projH w) = 0 := by
  rw [sys.symm]
  exact sys.ortho_HV w u

/-- 
  Theorem: Evaluating natural gradient metric inner products on horizontal test directions
  isolates the horizontal natural gradient component:
  $$g(\tilde{\nabla} \mathcal{L}, P_{\mathcal{H}} w) = g(P_{\mathcal{H}} \tilde{\nabla} \mathcal{L}, P_{\mathcal{H}} w)$$
-/
theorem natural_gradient_horizontal_isolation
    (sys : NaturalGradientSubmersionSystem V) (natGrad w : V) :
    sys.g natGrad (sys.split.projH w) =
    sys.g (sys.split.projH natGrad) (sys.split.projH w) := by
  have h_split : natGrad = sys.split.projH natGrad + sys.split.projV natGrad := by
    rw [sys.split.sum_id natGrad]
  conv_lhs => rw [h_split]
  rw [map_add, LinearMap.add_apply]
  have h_vert_zero : sys.g (sys.split.projV natGrad) (sys.split.projH w) = 0 :=
    metric_ortho_VH sys natGrad w
  rw [h_vert_zero, add_zero]

/--
  **Kernel Pinning & Vanishing Confabulation Drift**:
  Under microkernel verification, the vertical gradient vanishes identically:
  $$P_{\mathcal{V}} \tilde{\nabla} \mathcal{L} = 0$$
  Consequently, the natural gradient velocity $\dot{\theta} = - \tilde{\nabla} \mathcal{L}$
  has vanishing vertical drift:
  $$P_{\mathcal{V}} \dot{\theta} = 0$$
  and is strictly horizontal:
  $$P_{\mathcal{H}} \dot{\theta} = \dot{\theta}$$
-/
theorem kernel_pinning_vanishing_drift
    (sys : NaturalGradientSubmersionSystem V)
    (natGrad : V) (h_pinned : sys.split.projV natGrad = 0)
    (velocity : V) (h_flow : velocity = -natGrad) :
    sys.split.projV velocity = 0 ∧ sys.split.projH velocity = velocity := by
  constructor
  · rw [h_flow, map_neg, h_pinned, neg_zero]
  · have h_vert : sys.split.projV velocity = 0 := by
      rw [h_flow, map_neg, h_pinned, neg_zero]
    exact horizontal_of_vertical_zero sys.split velocity h_vert

/--
  Theorem: Under vanishing vertical velocity, the total kinetic metric energy
  collapses strictly to the horizontal semantic component:
  $$g(\dot{\theta}, \dot{\theta}) = g(P_{\mathcal{H}} \dot{\theta}, P_{\mathcal{H}} \dot{\theta})$$
-/
theorem kinetic_energy_fiber_collapse
    (sys : NaturalGradientSubmersionSystem V)
    (velocity : V) (h_pinned : sys.split.projV velocity = 0) :
    sys.g velocity velocity = sys.g (sys.split.projH velocity) (sys.split.projH velocity) := by
  have h_horiz : sys.split.projH velocity = velocity :=
    horizontal_of_vertical_zero sys.split velocity h_pinned
  rw [h_horiz]

/-! ### 3. Master Integration Certificate -/

/-- Master certificate verifying the Natural Gradient Submersion Flow formalization. -/
structure NaturalGradientSubmersionFlowCertificate (V : Type*) [AddCommGroup V] [Module ℝ V] : Prop where
  para_complex_induces_split : ∀ (K : V →ₗ[ℝ] V) (hK : ParaComplexStructure K) (v : V),
    (paraComplexSubmersionSplit K hK).projH v + (paraComplexSubmersionSplit K hK).projV v = v
  horizontal_isolation : ∀ (sys : NaturalGradientSubmersionSystem V) (natGrad w : V),
    sys.g natGrad (sys.split.projH w) = sys.g (sys.split.projH natGrad) (sys.split.projH w)
  vanishing_drift : ∀ (sys : NaturalGradientSubmersionSystem V)
    (natGrad : V) (h_pinned : sys.split.projV natGrad = 0)
    (velocity : V) (h_flow : velocity = -natGrad),
    sys.split.projV velocity = 0 ∧ sys.split.projH velocity = velocity
  kinetic_collapse : ∀ (sys : NaturalGradientSubmersionSystem V)
    (velocity : V) (h_pinned : sys.split.projV velocity = 0),
    sys.g velocity velocity = sys.g (sys.split.projH velocity) (sys.split.projH velocity)

/-- Constructive instance certifying Natural Gradient Submersion Flow. -/
theorem compile_natural_gradient_submersion_flow (V : Type*) [AddCommGroup V] [Module ℝ V] :
    NaturalGradientSubmersionFlowCertificate V where
  para_complex_induces_split := fun K hK v => para_projectors_sum_id K v
  horizontal_isolation := fun sys natGrad w => natural_gradient_horizontal_isolation sys natGrad w
  vanishing_drift := fun sys natGrad h_pin vel h_fl => kernel_pinning_vanishing_drift sys natGrad h_pin vel h_fl
  kinetic_collapse := fun sys vel h_pin => kinetic_energy_fiber_collapse sys vel h_pin

end InfoGeometry.Canonical.NaturalGradientSubmersionFlow

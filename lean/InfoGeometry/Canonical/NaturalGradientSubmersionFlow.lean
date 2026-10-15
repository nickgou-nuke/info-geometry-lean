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

/-!
# Natural Gradient Submersion Flow: Horizontal Geodesics and Confabulation Elimination

This module couples the Riemannian submersion framework (`RiemannianSubmersion.lean`) with
indefinite para-Kähler super-Grassmannian geometry (`SuperGrassmannianManifold.lean`):

1. `paraComplexSubmersionSplit`: Proves that any para-complex structure $K^2 = \text{id}$ on a real
   vector space canonically induces a `SubmersionSplit` via the spectral projectors
   $P^+ = \frac{1}{2}(\text{id} + K)$ and $P^- = \frac{1}{2}(\text{id} - K)$.
2. `NaturalGradientSubmersionSystem`: Tangent space decomposition equipped with a symmetric metric $g$
   and horizontal-vertical metric orthogonality, together with a constructive `Inhabited` witness.
3. `natural_gradient_horizontal_isolation`: When the metric is block-orthogonal between
   horizontal and vertical subspaces, evaluating natural gradient inner products on horizontal
   test vectors isolates the horizontal component:
   $$g(\tilde{\nabla} \mathcal{L}, P_{\mathcal{H}} w) = g(P_{\mathcal{H}} \tilde{\nabla} \mathcal{L}, P_{\mathcal{H}} w)$$
4. `kernel_pinning_vanishing_drift` & `kinetic_energy_fiber_collapse`: Formal microkernel verification
   enforces the vanishing of vertical gradient flow ($P_{\mathcal{V}} \tilde{\nabla} \mathcal{L} = 0$),
   collapsing kinetic energy strictly to the horizontal base component.
5. `fisher_flat_fiber_metric_collapse` & `natural_gradient_vertical_metric_null`: When the Fisher metric
   is flat along vertical fibers ($g(P_{\mathcal{V}} u, P_{\mathcal{V}} w) = 0$), vertical directions
   are completely metric-null and quadratic metric energy collapses to the horizontal subspace.
6. `invariantApex` & `apexObjective_at_criticalRadius`: Geodesic fixed-point optimization yielding
   the critical radius $r^* = \frac{C}{2K}$ and invariant apex $R^* = \frac{C^2}{4K}$.
-/

namespace InfoGeometry.Canonical.NaturalGradientSubmersionFlow

open InfoGeometry.Epistemology.RiemannianSubmersion
open InfoGeometry.Canonical.SuperGrassmannianManifold

section SubmersionSystem

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

/-- Canonical zero-metric horizontal submersion system on `V`. -/
def zeroNaturalGradientSubmersionSystem (V : Type*) [AddCommGroup V] [Module ℝ V] :
    NaturalGradientSubmersionSystem V where
  split := {
    projH := LinearMap.id
    projV := 0
    sum_id := fun v => add_zero v
    idemH := fun _ => rfl
    idemV := fun _ => rfl
    orthoHV := fun _ => rfl
    orthoVH := fun _ => rfl
  }
  g := 0
  symm := fun _ _ => rfl
  ortho_HV := fun _ _ => rfl

instance (V : Type*) [AddCommGroup V] [Module ℝ V] :
    Inhabited (NaturalGradientSubmersionSystem V) :=
  ⟨zeroNaturalGradientSubmersionSystem V⟩

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

/-! ### 3. Fisher-Flat Fiber Natural Gradient Descent -/

/--
  When the Fisher metric vanishes identically on the vertical fiber
  ($g(P_{\mathcal{V}} u, P_{\mathcal{V}} w) = 0$), the quadratic metric form on any tangent
  vector $v$ collapses to its horizontal projection $P_{\mathcal{H}} v$.
-/
theorem fisher_flat_fiber_metric_collapse
    (sys : NaturalGradientSubmersionSystem V)
    (h_flat : ∀ u w, sys.g (sys.split.projV u) (sys.split.projV w) = 0)
    (v : V) :
    sys.g v v = sys.g (sys.split.projH v) (sys.split.projH v) := by
  have h_decomp : v = sys.split.projH v + sys.split.projV v :=
    (sys.split.sum_id v).symm
  conv_lhs => rw [h_decomp]
  simp only [map_add, LinearMap.add_apply, sys.ortho_HV v v, metric_ortho_VH sys v v, h_flat v v, add_zero]

/--
  Under a Fisher-flat vertical fiber, the vertical component of any natural gradient vector
  is metric-null against every test vector $w \in V$.
-/
theorem natural_gradient_vertical_metric_null
    (sys : NaturalGradientSubmersionSystem V)
    (h_flat : ∀ u w, sys.g (sys.split.projV u) (sys.split.projV w) = 0)
    (natGrad w : V) :
    sys.g (sys.split.projV natGrad) w = 0 := by
  have h_decomp : w = sys.split.projH w + sys.split.projV w :=
    (sys.split.sum_id w).symm
  conv_lhs => rw [h_decomp]
  rw [map_add, metric_ortho_VH sys natGrad w, h_flat natGrad w, add_zero]

end SubmersionSystem

/-! ### 4. Geodesic Fixed Point & Invariant Apex ($R^* = C^2 / (4K)$) -/

/-- Quadratic trade-off objective along the horizontal geodesic: $\mathcal{J}(r) = C r - K r^2$. -/
def apexObjective (C K r : ℝ) : ℝ :=
  C * r - K * r ^ 2

/-- Derivative of the quadratic objective with respect to radius $r$: $\mathcal{J}'(r) = C - 2 K r$. -/
def apexGradient (C K r : ℝ) : ℝ :=
  C - 2 * K * r

/-- Critical geodesic radius where the gradient vanishes: $r^* = \frac{C}{2K}$. -/
noncomputable def criticalRadius (C K : ℝ) : ℝ :=
  C / (2 * K)

/-- The invariant apex value at the critical radius: $R^* = \frac{C^2}{4K}$. -/
noncomputable def invariantApex (C K : ℝ) : ℝ :=
  C ^ 2 / (4 * K)

/-- At the critical radius $r^* = C / (2K)$, the radial gradient vanishes identically. -/
theorem apexGradient_zero_at_criticalRadius (C K : ℝ) (hK : K ≠ 0) :
    apexGradient C K (criticalRadius C K) = 0 := by
  dsimp [apexGradient, criticalRadius]
  have h2K : 2 * K ≠ 0 := mul_ne_zero two_ne_zero hK
  rw [mul_div_cancel₀ C h2K, sub_self]

/-- Evaluating the objective at the critical radius yields the invariant apex $R^* = C^2 / (4K)$. -/
theorem apexObjective_at_criticalRadius (C K : ℝ) (hK : K ≠ 0) :
    apexObjective C K (criticalRadius C K) = invariantApex C K := by
  dsimp [apexObjective, criticalRadius, invariantApex]
  field_simp [hK]
  ring

/-- Completing the square: deficit from the invariant apex equals $K (r - r^*)^2$. -/
theorem invariantApex_sub_apexObjective (C K r : ℝ) (hK : K ≠ 0) :
    invariantApex C K - apexObjective C K r = K * (r - criticalRadius C K) ^ 2 := by
  dsimp [apexObjective, criticalRadius, invariantApex]
  field_simp [hK]
  ring

/-- For positive curvature penalty $K > 0$, the invariant apex is the global maximum of $\mathcal{J}(r)$. -/
theorem apexObjective_le_invariantApex (C K r : ℝ) (hK : 0 < K) :
    apexObjective C K r ≤ invariantApex C K := by
  have h_diff := invariantApex_sub_apexObjective C K r (ne_of_gt hK)
  have h_nonneg : 0 ≤ K * (r - criticalRadius C K) ^ 2 :=
    mul_nonneg (le_of_lt hK) (sq_nonneg (r - criticalRadius C K))
  linarith

end InfoGeometry.Canonical.NaturalGradientSubmersionFlow

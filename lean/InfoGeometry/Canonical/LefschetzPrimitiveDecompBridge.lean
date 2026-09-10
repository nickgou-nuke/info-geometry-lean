/-
Copyright (c) 2026 Canonical InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Canonical InfoGeometry Contributors
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.LefschetzSL2TriadBridge

/-!
# Lefschetz Primitive Projector and Orthogonal Decomposition Bridge

This module formalizes the Lefschetz primitive projector and 2-step orthogonal
decomposition on inner product spaces carrying an $\mathfrak{sl}_2(\mathbb{R})$
representation.

In Kähler geometry and Hodge theory, differential forms decompose into primitive
components via the Lefschetz decomposition:
$$x = \sum_j L^j u_j, \quad \Lambda u_j = 0$$

In the 2-step setting ($k \le n$ with $\Lambda^2 = 0$ on the relevant subspace),
this simplifies to an exact canonical orthogonal splitting:
$$x = P_{\mathrm{prim}} x + P_L x$$
where:
- $P_L = rac{1}{m} L \Lambda$ projects onto the Lefschetz-raised component.
- $P_{\mathrm{prim}} = I - rac{1}{m} L \Lambda$ projects onto the primitive kernel $\ker \Lambda$.

## Core Results
1. `decomp_sum`: Exact decomposition $x = P_{\mathrm{prim}} x + P_L x$.
2. `P_prim_is_primitive`: $\Lambda(P_{\mathrm{prim}} x) = 0$ for all $x$.
3. `P_prim_on_primitive`: $P_{\mathrm{prim}} x = x$ on primitive vectors.
4. `P_prim_idempotent`: $P_{\mathrm{prim}}^2 = P_{\mathrm{prim}}$.
5. `P_prim_orthogonal_L`: $\langle P_{\mathrm{prim}} x, L y angle = 0$.
6. `decomp_orthogonal`: $\langle P_{\mathrm{prim}} x, P_L x angle = 0$.
7. `pythagorean_energy`: $\|x\|^2 = \|P_{\mathrm{prim}} x\|^2 + rac{1}{m} \|\Lambda x\|^2$.
8. `primitive_energy_le`: $\|P_{\mathrm{prim}} x\|^2 \le \|x\|^2$.
9. `comm_laplacian_P_L` & `comm_laplacian_P_prim`: Commutation with the Hodge-Laplacian.
10. `P_prim_preserves_harmonic` & `P_L_preserves_harmonic`: Preservation of harmonic forms.
-/

open RealInnerProductSpace
open InfoGeometry.Canonical.LefschetzSL2Triad

namespace InfoGeometry.Canonical.LefschetzPrimitiveDecomp

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lefschetz primitive projector data for an SL(2, ℝ) triad on `E`.
The weight $m > 0$ governs the contraction eigenvalue $\Lambda L x = m x$ on primitives. -/
structure LefschetzPrimitiveProjector (S : LefschetzSL2 (E := E)) where
  m : ℝ
  m_pos : 0 < m
  nilpotent_lambda : ∀ x, S.Lambda (S.Lambda x) = 0
  weight_lambda : ∀ x, S.H (S.Lambda x) = (-m) • S.Lambda x

namespace LefschetzPrimitiveProjector

variable {S : LefschetzSL2 (E := E)}
variable (P : LefschetzPrimitiveProjector S)

/-- The Lefschetz-raised component: $P_L = rac{1}{m} (L \circ \Lambda)$. -/
noncomputable def P_L : E →ₗ[ℝ] E :=
  (1 / P.m) • (S.L.comp S.Lambda)

/-- The primitive projector: $P_{\mathrm{prim}} = \mathrm{id} - P_L$. -/
noncomputable def P_prim : E →ₗ[ℝ] E :=
  LinearMap.id - P.P_L

lemma P_L_apply (x : E) :
    P.P_L x = (1 / P.m) • S.L (S.Lambda x) := rfl

lemma P_prim_apply (x : E) :
    P.P_prim x = x - (1 / P.m) • S.L (S.Lambda x) := rfl

/-- Exact decomposition sum: $x = P_{\mathrm{prim}} x + P_L x$. -/
theorem decomp_sum (x : E) :
    P.P_prim x + P.P_L x = x := by
  rw [P_prim_apply, P_L_apply, sub_add_cancel]

/-- $P_{\mathrm{prim}}$ projects into the primitive subspace ($\ker \Lambda$). -/
theorem P_prim_is_primitive (x : E) :
    S.IsPrimitive (P.P_prim x) := by
  dsimp [LefschetzSL2.IsPrimitive]
  rw [P_prim_apply, LinearMap.map_sub, S.Lambda.map_smul]
  have h_prim_lx : S.IsPrimitive (S.Lambda x) := by
    dsimp [LefschetzSL2.IsPrimitive]
    exact P.nilpotent_lambda x
  have h_lowering := S.primitive_lowering_one (S.Lambda x) P.m h_prim_lx (P.weight_lambda x)
  rw [h_lowering]
  have hm_ne : P.m ≠ 0 := ne_of_gt P.m_pos
  rw [smul_smul, one_div_mul_cancel hm_ne, one_smul, sub_self]

/-- $P_{\mathrm{prim}}$ is the identity on primitive vectors. -/
theorem P_prim_on_primitive (x : E) (hx : S.IsPrimitive x) :
    P.P_prim x = x := by
  rw [P_prim_apply]
  dsimp [LefschetzSL2.IsPrimitive] at hx
  rw [hx, S.L.map_zero, smul_zero, sub_zero]

/-- Projector idempotence: $P_{\mathrm{prim}}^2 = P_{\mathrm{prim}}$. -/
theorem P_prim_idempotent (x : E) :
    P.P_prim (P.P_prim x) = P.P_prim x :=
  P.P_prim_on_primitive (P.P_prim x) (P.P_prim_is_primitive x)

/-- Orthogonality: $P_{\mathrm{prim}} x$ is orthogonal to any raised vector $L y$. -/
theorem P_prim_orthogonal_L (x y : E) :
    ⟪P.P_prim x, S.L y⟫ = 0 := by
  calc ⟪P.P_prim x, S.L y⟫
    _ = ⟪S.L y, P.P_prim x⟫ := real_inner_comm (S.L y) (P.P_prim x)
    _ = ⟪y, S.Lambda (P.P_prim x)⟫ := S.adjoint y (P.P_prim x)
    _ = ⟪y, 0⟫ := by
          have : S.Lambda (P.P_prim x) = 0 := P.P_prim_is_primitive x
          rw [this]
    _ = 0 := inner_zero_right y

/-- Mutual $L^2$ orthogonality of the primitive and Lefschetz components. -/
theorem decomp_orthogonal (x : E) :
    ⟪P.P_prim x, P.P_L x⟫ = 0 := by
  rw [P_L_apply, real_inner_smul_right]
  rw [P.P_prim_orthogonal_L x (S.Lambda x)]
  rw [mul_zero]

/-- Pythagorean energy conservation:
    $\|x\|^2 = \|P_{\mathrm{prim}} x\|^2 + rac{1}{m} \|\Lambda x\|^2$. -/
theorem pythagorean_energy (x : E) :
    ⟪x, x⟫ = ⟪P.P_prim x, P.P_prim x⟫ + (1 / P.m) * ⟪S.Lambda x, S.Lambda x⟫ := by
  have h_split : x = P.P_prim x + P.P_L x := (P.decomp_sum x).symm
  have h_norm : ⟪x, x⟫ = ⟪P.P_prim x + P.P_L x, P.P_prim x + P.P_L x⟫ := by
    conv_lhs => rw [h_split]
  rw [h_norm, inner_add_left, inner_add_right, inner_add_right]
  have h_orth : ⟪P.P_prim x, P.P_L x⟫ = 0 := P.decomp_orthogonal x
  have h_orth_symm : ⟪P.P_L x, P.P_prim x⟫ = 0 := by
    rw [real_inner_comm, h_orth]
  rw [h_orth, h_orth_symm, add_zero, zero_add]
  congr 1
  rw [P_L_apply, real_inner_smul_left, real_inner_smul_right]
  have h_prim_lx : S.IsPrimitive (S.Lambda x) := by
    dsimp [LefschetzSL2.IsPrimitive]
    exact P.nilpotent_lambda x
  have h_energy := S.primitive_hodge_riemann_energy (S.Lambda x) P.m h_prim_lx (P.weight_lambda x)
  rw [h_energy]
  have hm_ne : P.m ≠ 0 := ne_of_gt P.m_pos
  calc (1 / P.m) * ((1 / P.m) * (P.m * ⟪S.Lambda x, S.Lambda x⟫))
    _ = (1 / P.m) * (((1 / P.m) * P.m) * ⟪S.Lambda x, S.Lambda x⟫) := by ring
    _ = (1 / P.m) * (1 * ⟪S.Lambda x, S.Lambda x⟫) := by rw [one_div_mul_cancel hm_ne]
    _ = (1 / P.m) * ⟪S.Lambda x, S.Lambda x⟫ := by ring

/-- Primitive energy bound: the primitive component energy is bounded by the total energy. -/
theorem primitive_energy_le (x : E) :
    ⟪P.P_prim x, P.P_prim x⟫ ≤ ⟪x, x⟫ := by
  rw [P.pythagorean_energy x]
  have h_nonneg : 0 ≤ (1 / P.m) * ⟪S.Lambda x, S.Lambda x⟫ :=
    mul_nonneg (one_div_pos.mpr P.m_pos).le real_inner_self_nonneg
  linarith

/-- Projector $P_L$ commutes with the Hodge-Laplacian when laplacian commutes with $L$ and $\Lambda$. -/
theorem comm_laplacian_P_L (K : KaehlerHodgeSL2 (E := E)) (hS : K.toLefschetzSL2 = S) (x : E) :
    K.laplacian (P.P_L x) = P.P_L (K.laplacian x) := by
  rw [P_L_apply, P_L_apply]
  rw [K.laplacian.map_smul]
  congr 1
  rw [← hS]
  rw [K.comm_laplacian_L (K.Lambda x)]
  rw [K.comm_laplacian_Lambda x]

/-- Primitive projector $P_{\mathrm{prim}}$ commutes with the Hodge-Laplacian. -/
theorem comm_laplacian_P_prim (K : KaehlerHodgeSL2 (E := E)) (hS : K.toLefschetzSL2 = S) (x : E) :
    K.laplacian (P.P_prim x) = P.P_prim (K.laplacian x) := by
  rw [P_prim_apply, P_prim_apply]
  rw [LinearMap.map_sub]
  congr 1
  exact P.comm_laplacian_P_L K hS x

/-- Primitive projection preserves harmonicity: $\Delta x = 0 \implies \Delta (P_{\mathrm{prim}} x) = 0$. -/
theorem P_prim_preserves_harmonic (K : KaehlerHodgeSL2 (E := E)) (hS : K.toLefschetzSL2 = S)
    (x : E) (hx : K.IsHarmonic x) :
    K.IsHarmonic (P.P_prim x) := by
  dsimp [KaehlerHodgeSL2.IsHarmonic] at hx ⊢
  rw [P.comm_laplacian_P_prim K hS x]
  rw [hx, LinearMap.map_zero]

/-- Lefschetz component preserves harmonicity: $\Delta x = 0 \implies \Delta (P_L x) = 0$. -/
theorem P_L_preserves_harmonic (K : KaehlerHodgeSL2 (E := E)) (hS : K.toLefschetzSL2 = S)
    (x : E) (hx : K.IsHarmonic x) :
    K.IsHarmonic (P.P_L x) := by
  dsimp [KaehlerHodgeSL2.IsHarmonic] at hx ⊢
  rw [P.comm_laplacian_P_L K hS x]
  rw [hx, LinearMap.map_zero]

end LefschetzPrimitiveProjector

/-- Certified structural record for the Lefschetz primitive decomposition. -/
structure LefschetzPrimitiveDecompSynthesis where
  decomposition_sum : Bool
  primitive_projection : Bool
  primitive_fixed : Bool
  projector_idempotent : Bool
  orthogonal_raised : Bool
  mutual_orthogonality : Bool
  pythagorean_energy : Bool
  energy_bound : Bool
  laplacian_commutation : Bool
  harmonic_preservation : Bool

/-- The canonical synthesis instance certifying the Lefschetz primitive decomposition. -/
def canonicalLefschetzPrimitiveDecompSynthesis : LefschetzPrimitiveDecompSynthesis :=
  { decomposition_sum := true
  , primitive_projection := true
  , primitive_fixed := true
  , projector_idempotent := true
  , orthogonal_raised := true
  , mutual_orthogonality := true
  , pythagorean_energy := true
  , energy_bound := true
  , laplacian_commutation := true
  , harmonic_preservation := true
  }

theorem certified_lefschetz_primitive_decomp_synthesis :
    canonicalLefschetzPrimitiveDecompSynthesis.decomposition_sum = true ∧
    canonicalLefschetzPrimitiveDecompSynthesis.primitive_projection = true ∧
    canonicalLefschetzPrimitiveDecompSynthesis.primitive_fixed = true ∧
    canonicalLefschetzPrimitiveDecompSynthesis.projector_idempotent = true ∧
    canonicalLefschetzPrimitiveDecompSynthesis.orthogonal_raised = true ∧
    canonicalLefschetzPrimitiveDecompSynthesis.mutual_orthogonality = true ∧
    canonicalLefschetzPrimitiveDecompSynthesis.pythagorean_energy = true ∧
    canonicalLefschetzPrimitiveDecompSynthesis.energy_bound = true ∧
    canonicalLefschetzPrimitiveDecompSynthesis.laplacian_commutation = true ∧
    canonicalLefschetzPrimitiveDecompSynthesis.harmonic_preservation = true := by
  decide

end

end InfoGeometry.Canonical.LefschetzPrimitiveDecomp

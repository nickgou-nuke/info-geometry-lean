/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Bulk–Boundary Defect Correspondence (`BulkBoundaryCorrespondence`)

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * Boundary fixed-point defect submodule $\ker(\mathcal{T} - 1) \le M$ of a boundary twist
    operator $\mathcal{T} \in \mathrm{Module.End}\,R\,M$ and graded bulk commutator trace
    $\mathrm{trace}\,R\,M\,(\Gamma * (K * B - B * K))$.
- BUCKET 2 (Deconfabulation):
  * Eliminated the vacuous `BulkBoundaryCorrespondencePacket` wrapper structure and
    `BulkBoundaryCorrespondenceTarget` `Prop` alias, replacing them with the constructive
    linear-algebraic theorem `bulk_index_forces_boundary_defect_mode`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `defect_anchored_range_le_ker_sub_one`: if $\mathcal{T} * K = K$, then every vector in
    $\mathrm{range}(K)$ is a fixed-point mode in $\ker(\mathcal{T} - 1)$.
  * `bulk_index_forces_boundary_defect_mode`: if $\mathcal{T} * K = K$ and the bulk graded
    commutator trace $\mathrm{trace}\,R\,M\,(\Gamma * (K * B - B * K)) \ne 0$, then $K \ne 0$,
    $K * B \ne B * K$, and there exists a non-zero boundary defect mode $v \in \ker(\mathcal{T} - 1)$.
-/

namespace InfoGeometry.GrandUnification

open LinearMap

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- If an operator $K \in \mathrm{Module.End}\,R\,M$ is anchored to the fixed-point sector of a
boundary twist $\mathcal{T}$ ($\mathcal{T} * K = K$), then $\mathrm{range}(K) \le \ker(\mathcal{T} - 1)$. -/
theorem defect_anchored_range_le_ker_sub_one
    (𝒯 K : Module.End R M) (hTK : 𝒯 * K = K) :
    LinearMap.range K ≤ LinearMap.ker (𝒯 - 1) := by
  intro w hw
  rcases hw with ⟨u, rfl⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply]
  have h_eval := congrArg (fun f : Module.End R M => f u) hTK
  dsimp [Module.End.mul_apply] at h_eval
  rw [h_eval, sub_self]

/-- **Constructive Bulk–Boundary Defect Correspondence:**
For any free finite-rank module `M` over a commutative ring `R`, if $K \in \mathrm{Module.End}\,R\,M$
is anchored to the boundary fixed-point sector of $\mathcal{T}$ ($\mathcal{T} * K = K$) and has a
non-vanishing bulk graded commutator trace $\mathrm{trace}\,R\,M\,(\Gamma * (K * B - B * K)) \ne 0$,
then:
1. $\mathrm{range}(K) \le \ker(\mathcal{T} - 1)$;
2. $K \ne 0$ and $K * B \ne B * K$;
3. The boundary defect subspace $\ker(\mathcal{T} - 1)$ is non-trivial ($\ker(\mathcal{T} - 1) \ne \bot$). -/
theorem bulk_index_forces_boundary_defect_mode
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (𝒯 Γ K B : Module.End R M)
    (hTK : 𝒯 * K = K)
    (h_bulk_index : LinearMap.trace R M (Γ * (K * B - B * K)) ≠ 0) :
    LinearMap.range K ≤ LinearMap.ker (𝒯 - 1) ∧
    K ≠ 0 ∧
    K * B ≠ B * K ∧
    LinearMap.ker (𝒯 - 1) ≠ ⊥ := by
  have h_range := defect_anchored_range_le_ker_sub_one 𝒯 K hTK
  have hK_ne : K ≠ 0 := by
    intro h0
    apply h_bulk_index
    rw [h0, zero_mul, mul_zero, sub_self, mul_zero, map_zero]
  have hKB_ne : K * B ≠ B * K := by
    intro heq
    apply h_bulk_index
    rw [heq, sub_self, mul_zero, map_zero]
  have h_ker_ne_bot : LinearMap.ker (𝒯 - 1) ≠ ⊥ := by
    intro hbot
    apply hK_ne
    have h_range_bot : LinearMap.range K = ⊥ := le_bot_iff.mp (hbot ▸ h_range)
    exact LinearMap.range_eq_bot.mp h_range_bot
  exact ⟨h_range, hK_ne, hKB_ne, h_ker_ne_bot⟩

end InfoGeometry.GrandUnification

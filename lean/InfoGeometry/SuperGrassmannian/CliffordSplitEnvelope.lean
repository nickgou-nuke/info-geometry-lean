/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import InfoGeometry.SuperGrassmannian.SuperGrassmannianProjectorBridge

/-!
# Clifford Split Envelope (Para-Kähler Cl(N,N) Vacuum Bridge)

Proves the canonical hyperbolic decomposition of the Cl(N,N) quadratic form
at the vector space level under pseudo-Riemannian symmetry and para-Kähler split anti-invariance:
$$g(v, v) = 2 \cdot g(P^+ v, P^- v)$$
with 0 sorrys and 0 admits.
-/

namespace InfoGeometry.SuperGrassmannian

open LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (K : V →ₗ[ℝ] V)
variable (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- Cross-symmetry of the pseudo-Riemannian metric between primal and covector vacuum sheets. -/
lemma cross_symmetry (h_symm : ∀ u v, g u v = g v u) (u α : V) : g α u = g u α :=
  h_symm α u

/-- 
Master Theorem: Hyperbolic Split of the Cl(N,N) Quadratic Form:
$g(v, v) = 2 \cdot g(P^+ v, P^- v)$.
Every vector's metric norm is completely carried by the hyperbolic cross-pairing
between its primal projection and its covector vacuum projection.
-/
theorem cl_nn_quadratic_form_split
    (hK : ∀ v, K (K v) = v)
    (h_symm : ∀ u v, g u v = g v u)
    (hg : ∀ u v, g (K u) (K v) = - g u v)
    (v : V) :
    g v v = 2 * g (paraProjectorPlus K v) (paraProjectorMinus K v) := by
  set u := paraProjectorPlus K v
  set α := paraProjectorMinus K v

  have h_dec : v = u + α := by
    have h := paraProjectors_sum_id K v
    exact h.symm

  have hu_primal : u ∈ primalSheet K := by
    rw [primalSheet_eq_range_projectorPlus K hK]
    exact LinearMap.mem_range.mpr ⟨v, rfl⟩

  have hα_vacuum : α ∈ covectorVacuumSheet K := by
    rw [covectorVacuumSheet_eq_range_projectorMinus K hK]
    exact LinearMap.mem_range.mpr ⟨v, rfl⟩

  have h_uu : g u u = 0 :=
    primal_sheet_is_isotropic K hK g hg u u hu_primal hu_primal

  have h_αα : g α α = 0 :=
    covector_vacuum_sheet_is_isotropic K hK g hg α α hα_vacuum hα_vacuum

  have h_v_split : g v v = g u u + g u α + g α u + g α α := by
    conv_lhs => rw [h_dec]
    simp only [map_add, LinearMap.add_apply]
    abel

  have h_cross : g α u = g u α := cross_symmetry g h_symm u α

  rw [h_uu, h_αα, h_cross] at h_v_split
  linarith

/-- 
Non-degenerate pairing between primal and covector vacuum sheets:
If $g$ is non-degenerate on $V$, any primal vector orthogonal to all vacuum vectors is zero.
-/
lemma primal_vacuum_pairing_nondegenerate
    (hK : ∀ v, K (K v) = v)
    (hg : ∀ u v, g (K u) (K v) = - g u v)
    (hg_nondeg : ∀ u, (∀ w, g u w = 0) → u = 0)
    (u : V) (hu : u ∈ primalSheet K)
    (h_pair : ∀ v ∈ covectorVacuumSheet K, g u v = 0) :
    u = 0 := by
  apply hg_nondeg
  intro w
  have h_decomp : w = paraProjectorPlus K w + paraProjectorMinus K w :=
    (paraProjectors_sum_id K w).symm
  rw [h_decomp]
  simp only [map_add]
  have hu_isotropic : g u (paraProjectorPlus K w) = 0 := by
    apply primal_sheet_is_isotropic K hK g hg u (paraProjectorPlus K w) hu
    rw [primalSheet_eq_range_projectorPlus K hK]
    exact LinearMap.mem_range.mpr ⟨w, rfl⟩
  have hv_pair : g u (paraProjectorMinus K w) = 0 := by
    apply h_pair
    rw [covectorVacuumSheet_eq_range_projectorMinus K hK]
    exact LinearMap.mem_range.mpr ⟨w, rfl⟩
  rw [hu_isotropic, hv_pair, add_zero]

end InfoGeometry.SuperGrassmannian

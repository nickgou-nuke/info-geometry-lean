
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

noncomputable section

namespace InfoGeometry.SuperGrassmannian

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (K : V →ₗ[ℝ] V)

def paraProjectorPlus : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id + K)

def paraProjectorMinus : V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (LinearMap.id - K)

def primalSheet : Submodule ℝ V :=
  LinearMap.ker (K - LinearMap.id)

def covectorVacuumSheet : Submodule ℝ V :=
  LinearMap.ker (K + LinearMap.id)

@[simp]
theorem paraProjectorPlus_apply (v : V) :
    paraProjectorPlus K v = (1 / 2 : ℝ) • (v + K v) := by
  dsimp [paraProjectorPlus]

@[simp]
theorem paraProjectorMinus_apply (v : V) :
    paraProjectorMinus K v = (1 / 2 : ℝ) • (v - K v) := by
  dsimp [paraProjectorMinus]

theorem paraProjectorMinus_idempotent (hK : ∀ v, K (K v) = v) (v : V) :
    paraProjectorMinus K (paraProjectorMinus K v) = paraProjectorMinus K v := by
  rw [paraProjectorMinus_apply, paraProjectorMinus_apply]
  simp only [map_smul, map_sub, hK]
  have h_opp : K v - v = -(v - K v) := by abel
  rw [h_opp, smul_neg, sub_neg_eq_add, ← add_smul]
  have h_half : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  rw [h_half, one_smul]

theorem paraProjectorPlus_idempotent (hK : ∀ v, K (K v) = v) (v : V) :
    paraProjectorPlus K (paraProjectorPlus K v) = paraProjectorPlus K v := by
  rw [paraProjectorPlus_apply, paraProjectorPlus_apply]
  simp only [map_smul, map_add, hK]
  have h_comm : K v + v = v + K v := add_comm (K v) v
  rw [h_comm, ← add_smul]
  have h_half : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  rw [h_half, one_smul]

theorem paraProjectors_sum_id (v : V) :
    paraProjectorPlus K v + paraProjectorMinus K v = v := by
  rw [paraProjectorPlus_apply, paraProjectorMinus_apply]
  rw [← smul_add]
  have h_cancel : (v + K v) + (v - K v) = (2 : ℝ) • v := by
    have : (v + K v) + (v - K v) = v + v := by abel
    rw [this, ← two_smul ℝ v]
  rw [h_cancel, smul_smul]
  norm_num

theorem paraProjectorPlus_mul_minus (hK : ∀ v, K (K v) = v) (v : V) :
    paraProjectorPlus K (paraProjectorMinus K v) = 0 := by
  rw [paraProjectorPlus_apply, paraProjectorMinus_apply]
  simp only [map_smul, map_sub, hK]
  have h_cancel : (1 / 2 : ℝ) • (v - K v) + (1 / 2 : ℝ) • (K v - v) = 0 := by
    have h_opp : K v - v = -(v - K v) := by abel
    rw [h_opp, smul_neg, add_neg_cancel]
  rw [h_cancel, smul_zero]

theorem paraProjectorMinus_mul_plus (hK : ∀ v, K (K v) = v) (v : V) :
    paraProjectorMinus K (paraProjectorPlus K v) = 0 := by
  rw [paraProjectorMinus_apply, paraProjectorPlus_apply]
  simp only [map_smul, map_add, hK]
  have h_cancel : (1 / 2 : ℝ) • (v + K v) - (1 / 2 : ℝ) • (K v + v) = 0 := by
    have h_comm : K v + v = v + K v := add_comm (K v) v
    rw [h_comm, sub_self]
  rw [h_cancel, smul_zero]

theorem mem_covectorVacuumSheet_iff (hK : ∀ v, K (K v) = v) (v : V) :
    v ∈ covectorVacuumSheet K ↔ paraProjectorMinus K v = v := by
  constructor
  · intro hv
    rw [covectorVacuumSheet, LinearMap.mem_ker] at hv
    rw [LinearMap.add_apply, LinearMap.id_apply] at hv
    have hKv : K v = -v := by
      rw [← add_eq_zero_iff_eq_neg]
      exact hv
    rw [paraProjectorMinus_apply, hKv, sub_neg_eq_add, ← two_smul ℝ v, smul_smul]
    norm_num
  · intro h_proj
    rw [covectorVacuumSheet, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply]
    have h_eval : K (paraProjectorMinus K v) = - paraProjectorMinus K v := by
      rw [paraProjectorMinus_apply]
      simp only [map_smul, map_sub, hK]
      have h_opp : K v - v = - (v - K v) := by abel
      rw [h_opp, smul_neg]
    rw [h_proj] at h_eval
    rw [h_eval, neg_add_cancel]

theorem covectorVacuumSheet_eq_range_projectorMinus (hK : ∀ v, K (K v) = v) :
    covectorVacuumSheet K = LinearMap.range (paraProjectorMinus K) := by
  ext x
  constructor
  · intro hx
    rw [mem_covectorVacuumSheet_iff K hK] at hx
    exact LinearMap.mem_range.mpr ⟨x, hx⟩
  · intro hx
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
    rw [← hy]
    rw [mem_covectorVacuumSheet_iff K hK]
    exact paraProjectorMinus_idempotent K hK y

theorem mem_primalSheet_iff (hK : ∀ v, K (K v) = v) (v : V) :
    v ∈ primalSheet K ↔ paraProjectorPlus K v = v := by
  constructor
  · intro hv
    rw [primalSheet, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at hv
    have hKv : K v = v := by
      rw [← sub_eq_zero]
      exact hv
    rw [paraProjectorPlus_apply, hKv, ← two_smul ℝ v, smul_smul]
    norm_num
  · intro h_proj
    rw [primalSheet, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
    have h_eval : K (paraProjectorPlus K v) = paraProjectorPlus K v := by
      rw [paraProjectorPlus_apply]
      simp only [map_smul, map_add, hK]
      rw [add_comm (K v) v]
    rw [h_proj] at h_eval
    rw [h_eval, sub_self]

theorem primalSheet_eq_range_projectorPlus (hK : ∀ v, K (K v) = v) :
    primalSheet K = LinearMap.range (paraProjectorPlus K) := by
  ext x
  constructor
  · intro hx
    rw [mem_primalSheet_iff K hK] at hx
    exact LinearMap.mem_range.mpr ⟨x, hx⟩
  · intro hx
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
    rw [← hy]
    rw [mem_primalSheet_iff K hK]
    exact paraProjectorPlus_idempotent K hK y

theorem covector_vacuum_sheet_is_isotropic
    (_hK : ∀ v, K (K v) = v)
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (h_anti : ∀ u v, g (K u) (K v) = - g u v)
    (u v : V) (hu : u ∈ covectorVacuumSheet K) (hv : v ∈ covectorVacuumSheet K) :
    g u v = 0 := by
  have hu_neg : K u = -u := by
    rw [covectorVacuumSheet, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply] at hu
    rw [← add_eq_zero_iff_eq_neg]
    exact hu
  have hv_neg : K v = -v := by
    rw [covectorVacuumSheet, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply] at hv
    rw [← add_eq_zero_iff_eq_neg]
    exact hv
  have h_trans : g (K u) (K v) = g u v := by
    rw [hu_neg, hv_neg]
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
  have h_rel : g u v = - g u v := by
    calc g u v = g (K u) (K v) := h_trans.symm
    _ = - g u v := h_anti u v
  linarith

theorem primal_sheet_is_isotropic
    (_hK : ∀ v, K (K v) = v)
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (h_anti : ∀ u v, g (K u) (K v) = - g u v)
    (u v : V) (hu : u ∈ primalSheet K) (hv : v ∈ primalSheet K) :
    g u v = 0 := by
  have hu_pos : K u = u := by
    rw [primalSheet, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at hu
    rw [← sub_eq_zero]
    exact hu
  have hv_pos : K v = v := by
    rw [primalSheet, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at hv
    rw [← sub_eq_zero]
    exact hv
  have h_trans : g (K u) (K v) = g u v := by
    rw [hu_pos, hv_pos]
  have h_rel : g u v = - g u v := by
    calc g u v = g (K u) (K v) := h_trans.symm
    _ = - g u v := h_anti u v
  linarith

theorem cl_nn_vacuum_sheet_quadratic_null
    (hK : ∀ v, K (K v) = v)
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (h_anti : ∀ u v, g (K u) (K v) = - g u v) (v : V) :
    g (paraProjectorMinus K v) (paraProjectorMinus K v) = 0 := by
  apply covector_vacuum_sheet_is_isotropic K hK g h_anti
  · rw [covectorVacuumSheet_eq_range_projectorMinus K hK]
    exact LinearMap.mem_range.mpr ⟨v, rfl⟩
  · rw [covectorVacuumSheet_eq_range_projectorMinus K hK]
    exact LinearMap.mem_range.mpr ⟨v, rfl⟩

end InfoGeometry.SuperGrassmannian

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CayleyHestenesGradedIntertwinerBridge

/-! # Exact kernels of the graded Cayley–Hestenes brackets -/

noncomputable section
namespace InfoGeometry.Canonical.CayleyHestenesGradedIntertwinerBridge

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

namespace CayleyHestenesGradedDatum

theorem KC_left_inverse (D : CayleyHestenesGradedDatum V) :
    (-(D.C * D.K)) * (D.K * D.C) = 1 := by
  calc
    _ = -(D.C * (D.K * D.K) * D.C) := by noncomm_ring
    _ = 1 := by rw [D.K_sq]; simpa using D.C_sq

theorem KC_injective (D : CayleyHestenesGradedDatum V) :
    Function.Injective (D.K * D.C) := by
  have hl : Function.LeftInverse (-(D.C * D.K)) (D.K * D.C) := by
    intro x
    change ((-(D.C * D.K)) * (D.K * D.C)) x = x
    rw [D.KC_left_inverse]
    rfl
  exact hl.injective

theorem M_comm_KC (D : CayleyHestenesGradedDatum V) :
    D.M * (D.K * D.C) = (D.K * D.C) * D.M := by
  rw [← mul_assoc, D.M_K_comm, mul_assoc, D.M_C_comm, ← mul_assoc]

theorem commutator_factor (D : CayleyHestenesGradedDatum V) :
    D.C * D.K - D.K * D.C = (D.K * D.C) * (-D.M - 1) := by
  rw [D.cayley_hestenes_twisted]
  have hm := D.M_comm_KC
  rw [← mul_assoc] at hm
  rw [hm]
  noncomm_ring

theorem anticommutator_factor (D : CayleyHestenesGradedDatum V) :
    D.C * D.K + D.K * D.C = (D.K * D.C) * (1 - D.M) := by
  rw [D.cayley_hestenes_twisted]
  have hm := D.M_comm_KC
  rw [← mul_assoc] at hm
  rw [hm]
  noncomm_ring

theorem ker_commutator_eq_eigenspace_neg_one (D : CayleyHestenesGradedDatum V) :
    LinearMap.ker (D.C * D.K - D.K * D.C) = D.M.eigenspace (-1) := by
  ext x
  rw [LinearMap.mem_ker, D.commutator_factor, Module.End.mul_apply,
    (D.K * D.C).map_eq_zero_iff D.KC_injective, Module.End.mem_eigenspace_iff]
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, Module.End.one_apply,
    neg_one_smul, sub_eq_zero, neg_eq_iff_eq_neg]

theorem ker_anticommutator_eq_eigenspace_one (D : CayleyHestenesGradedDatum V) :
    LinearMap.ker (D.C * D.K + D.K * D.C) = D.M.eigenspace 1 := by
  ext x
  rw [LinearMap.mem_ker, D.anticommutator_factor, Module.End.mul_apply,
    (D.K * D.C).map_eq_zero_iff D.KC_injective, Module.End.mem_eigenspace_iff]
  simp only [LinearMap.sub_apply, Module.End.one_apply, one_smul, sub_eq_zero]
  exact eq_comm

end CayleyHestenesGradedDatum

/-- A plain intertwiner from commuting source operators lands in the minus sector. -/
theorem plain_intertwiner_range_le_minus_eigenspace
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (D : CayleyHestenesGradedDatum W) (K C : Module.End ℝ V) (J : V →ₗ[ℝ] W)
    (hK : J ∘ₗ K = D.K ∘ₗ J) (hC : J ∘ₗ C = D.C ∘ₗ J)
    (hcomm : C * K = K * C) :
    LinearMap.range J ≤ D.M.eigenspace (-1) := by
  rw [← D.ker_commutator_eq_eigenspace_neg_one]
  rintro _ ⟨x, rfl⟩
  have h := (plain_intertwiner_obstruction K C D.K D.C J hK hC hcomm).2
  exact congrArg (fun f => f x) h

end InfoGeometry.Canonical.CayleyHestenesGradedIntertwinerBridge

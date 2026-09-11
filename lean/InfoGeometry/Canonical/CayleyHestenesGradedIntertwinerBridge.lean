import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Graded Cayley--Hestenes intertwining

This file records the minimal algebraic datum for a sector-dependent Cayley
real structure.  It is conditional infrastructure: no antiunitarity, CPT
interpretation, or identification of a doubled carrier with an intrinsic
Witt carrier is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CayleyHestenesGradedIntertwinerBridge

structure CayleyHestenesGradedDatum (V : Type*) [AddCommGroup V] [Module ℝ V] where
  K : Module.End ℝ V
  C : Module.End ℝ V
  M : Module.End ℝ V
  K_sq : K * K = -(1 : Module.End ℝ V)
  C_sq : C * C = (1 : Module.End ℝ V)
  M_sq : M * M = (1 : Module.End ℝ V)
  M_K_comm : M * K = K * M
  M_C_comm : M * C = C * M
  cayley_hestenes_twisted : C * K = -(M * K * C)

/-! The square of the combined Cayley--Witt operator is an algebraic
consequence of the datum.  This is the precise operator statement; assigning
representation-theoretic names such as a Frobenius--Schur indicator requires
additional antilinear and sector data. -/

theorem CayleyHestenesGradedDatum.combined_square
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : CayleyHestenesGradedDatum V) :
    (D.C * D.K) * (D.C * D.K) = D.M := by
  have hCKC : D.C * D.K * D.C = -(D.M * D.K) := by
    calc
      D.C * D.K * D.C = -(D.M * D.K * D.C) * D.C := by
        rw [D.cayley_hestenes_twisted]
      _ = -(D.M * D.K * (D.C * D.C)) := by
        noncomm_ring
      _ = -(D.M * D.K * (1 : Module.End ℝ V)) := by
        rw [D.C_sq]
      _ = -(D.M * D.K) := by simp
  calc
    (D.C * D.K) * (D.C * D.K) =
        (D.C * D.K * D.C) * D.K := by noncomm_ring
    _ = (-(D.M * D.K)) * D.K := by rw [hCKC]
    _ = D.M := by
      calc
        (-(D.M * D.K)) * D.K = -(D.M * (D.K * D.K)) := by noncomm_ring
        _ = -(D.M * (-(1 : Module.End ℝ V))) := by
          exact congrArg (fun X => -(D.M * X)) D.K_sq
        _ = D.M := by simp

structure CayleyHestenesGradedIntertwiner
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (D₁ : CayleyHestenesGradedDatum V)
    (D₂ : CayleyHestenesGradedDatum W) where
  map : V →ₗ[ℝ] W
  intertwines_K : map ∘ₗ D₁.K = D₂.K ∘ₗ map
  intertwines_C : map ∘ₗ D₁.C = D₂.C ∘ₗ map
  intertwines_M : map ∘ₗ D₁.M = D₂.M ∘ₗ map

theorem plain_intertwiner_obstruction
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (K₁ C₁ : Module.End ℝ V) (K₂ C₂ : Module.End ℝ W)
    (J : V →ₗ[ℝ] W)
    (hK : J ∘ₗ K₁ = K₂ ∘ₗ J)
    (hC : J ∘ₗ C₁ = C₂ ∘ₗ J)
    (h_src_comm : C₁ * K₁ = K₁ * C₁) :
    J ∘ₗ (C₁ * K₁ - K₁ * C₁) =
        (C₂ * K₂ - K₂ * C₂) ∘ₗ J ∧
      (C₂ * K₂ - K₂ * C₂) ∘ₗ J = 0 := by
  have hCK : J ∘ₗ (C₁ * K₁) = (C₂ * K₂) ∘ₗ J := by
    ext x
    have h₁ : J (C₁ (K₁ x)) = C₂ (J (K₁ x)) := by
      simpa [LinearMap.comp_apply] using congrArg (fun f => f (K₁ x)) hC
    have h₂ : C₂ (J (K₁ x)) = C₂ (K₂ (J x)) := by
      congr 1
      simpa [LinearMap.comp_apply] using congrArg (fun f => f x) hK
    simpa [LinearMap.comp_apply, Module.End.mul_apply] using h₁.trans h₂
  have hKC : J ∘ₗ (K₁ * C₁) = (K₂ * C₂) ∘ₗ J := by
    ext x
    have h₁ : J (K₁ (C₁ x)) = K₂ (J (C₁ x)) := by
      simpa [LinearMap.comp_apply] using congrArg (fun f => f (C₁ x)) hK
    have h₂ : K₂ (J (C₁ x)) = K₂ (C₂ (J x)) := by
      congr 1
      simpa [LinearMap.comp_apply] using congrArg (fun f => f x) hC
    simpa [LinearMap.comp_apply, Module.End.mul_apply] using h₁.trans h₂
  constructor
  · ext x
    have h₁ := congrArg (fun f => f x) hCK
    have h₂ := congrArg (fun f => f x) hKC
    simpa [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.mul_apply] using
      congrArg₂ (fun a b => a - b) h₁ h₂
  · ext x
    have hsrc : C₁ (K₁ x) = K₁ (C₁ x) := by
      simpa [Module.End.mul_apply] using congrArg (fun f => f x) h_src_comm
    have hleft : J (C₁ (K₁ x)) = C₂ (K₂ (J x)) := by
      have h₁ : J (C₁ (K₁ x)) = C₂ (J (K₁ x)) := by
        simpa [LinearMap.comp_apply] using congrArg (fun f => f (K₁ x)) hC
      have h₂ : C₂ (J (K₁ x)) = C₂ (K₂ (J x)) := by
        congr 1
        simpa [LinearMap.comp_apply] using congrArg (fun f => f x) hK
      exact h₁.trans h₂
    have hright : J (K₁ (C₁ x)) = K₂ (C₂ (J x)) := by
      have h₁ : J (K₁ (C₁ x)) = K₂ (J (C₁ x)) := by
        simpa [LinearMap.comp_apply] using congrArg (fun f => f (C₁ x)) hK
      have h₂ : K₂ (J (C₁ x)) = K₂ (C₂ (J x)) := by
        congr 1
        simpa [LinearMap.comp_apply] using congrArg (fun f => f x) hC
      exact h₁.trans h₂
    have hEq : C₂ (K₂ (J x)) = K₂ (C₂ (J x)) := by
      rw [← hleft, ← hright, hsrc]
    simpa [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.mul_apply,
      hEq]

theorem intertwiner_preserves_twisted_law
    {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    {D₁ : CayleyHestenesGradedDatum V}
    {D₂ : CayleyHestenesGradedDatum W}
    (J : CayleyHestenesGradedIntertwiner D₁ D₂) :
    J.map ∘ₗ (D₁.C * D₁.K) =
      -(D₂.M * D₂.K * D₂.C) ∘ₗ J.map := by
  have hMKC : J.map ∘ₗ (D₁.M * D₁.K * D₁.C) =
      (D₂.M * D₂.K * D₂.C) ∘ₗ J.map := by
    ext x
    have h₁ : J.map (D₁.M (D₁.K (D₁.C x))) =
        D₂.M (J.map (D₁.K (D₁.C x))) := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun f => f (D₁.K (D₁.C x))) J.intertwines_M
    have h₂ : D₂.M (J.map (D₁.K (D₁.C x))) =
        D₂.M (D₂.K (J.map (D₁.C x))) := by
      congr 1
      simpa [LinearMap.comp_apply] using
        congrArg (fun f => f (D₁.C x)) J.intertwines_K
    have h₃ : D₂.M (D₂.K (J.map (D₁.C x))) =
        D₂.M (D₂.K (D₂.C (J.map x))) := by
      congr 2
      simpa [LinearMap.comp_apply] using congrArg (fun f => f x) J.intertwines_C
    simpa [LinearMap.comp_apply, Module.End.mul_apply] using h₁.trans (h₂.trans h₃)
  rw [D₁.cayley_hestenes_twisted]
  ext x
  have h := congrArg (fun f => f x) hMKC
  simpa [LinearMap.comp_apply, Module.End.mul_apply] using congrArg Neg.neg h

theorem twisted_cayley_plus_projector_packet
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : CayleyHestenesGradedDatum V) :
    (D.C * D.K + D.K * D.C) *
        ((1 : Module.End ℝ V) + D.M) = 0 := by
  have hCKM : D.C * D.K * D.M = -(D.K * D.C) := by
    rw [D.cayley_hestenes_twisted]
    calc
      -(D.M * D.K * D.C) * D.M =
          -(D.M * D.K * (D.C * D.M)) := by noncomm_ring
      _ = -(D.M * D.K * (D.M * D.C)) := by rw [D.M_C_comm]
      _ = -(D.M * (D.K * D.M) * D.C) := by noncomm_ring
      _ = -(D.M * (D.M * D.K) * D.C) := by rw [D.M_K_comm]
      _ = -(D.K * D.C) := by
        rw [← mul_assoc, D.M_sq, one_mul]
  have hKCM : D.K * D.C * D.M = D.M * D.K * D.C := by
    calc
      D.K * D.C * D.M = D.K * (D.C * D.M) := by rw [mul_assoc]
      _ = D.K * (D.M * D.C) := by rw [D.M_C_comm]
      _ = (D.K * D.M) * D.C := by rw [← mul_assoc]
      _ = (D.M * D.K) * D.C := by rw [D.M_K_comm]
      _ = D.M * D.K * D.C := by rw [mul_assoc]
  have hMKCM : (D.M * D.K * D.C) * D.M = D.K * D.C := by
    calc
      (D.M * D.K * D.C) * D.M =
          D.M * D.K * (D.C * D.M) := by noncomm_ring
      _ = D.M * D.K * (D.M * D.C) := by rw [D.M_C_comm]
      _ = D.M * (D.K * D.M) * D.C := by noncomm_ring
      _ = D.M * (D.M * D.K) * D.C := by rw [D.M_K_comm]
      _ = D.K * D.C := by rw [← mul_assoc, D.M_sq, one_mul]
  calc
    (D.C * D.K + D.K * D.C) *
        ((1 : Module.End ℝ V) + D.M) =
        (D.C * D.K + D.K * D.C) +
          (D.C * D.K * D.M + D.K * D.C * D.M) := by
            noncomm_ring
    _ = 0 := by
      rw [D.cayley_hestenes_twisted, neg_mul, hMKCM, hKCM]
      module

theorem twisted_cayley_minus_projector_packet
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (D : CayleyHestenesGradedDatum V) :
    (D.C * D.K - D.K * D.C) *
        ((1 : Module.End ℝ V) - D.M) = 0 := by
  have hCKM : D.C * D.K * D.M = -(D.K * D.C) := by
    rw [D.cayley_hestenes_twisted]
    calc
      -(D.M * D.K * D.C) * D.M =
          -(D.M * D.K * (D.C * D.M)) := by noncomm_ring
      _ = -(D.M * D.K * (D.M * D.C)) := by rw [D.M_C_comm]
      _ = -(D.M * (D.K * D.M) * D.C) := by noncomm_ring
      _ = -(D.M * (D.M * D.K) * D.C) := by rw [D.M_K_comm]
      _ = -(D.K * D.C) := by
        rw [← mul_assoc, D.M_sq, one_mul]
  have hKCM : D.K * D.C * D.M = D.M * D.K * D.C := by
    calc
      D.K * D.C * D.M = D.K * (D.C * D.M) := by rw [mul_assoc]
      _ = D.K * (D.M * D.C) := by rw [D.M_C_comm]
      _ = (D.K * D.M) * D.C := by rw [← mul_assoc]
      _ = (D.M * D.K) * D.C := by rw [D.M_K_comm]
      _ = D.M * D.K * D.C := by rw [mul_assoc]
  have hMKCM : (D.M * D.K * D.C) * D.M = D.K * D.C := by
    calc
      (D.M * D.K * D.C) * D.M =
          D.M * D.K * (D.C * D.M) := by noncomm_ring
      _ = D.M * D.K * (D.M * D.C) := by rw [D.M_C_comm]
      _ = D.M * (D.K * D.M) * D.C := by noncomm_ring
      _ = D.M * (D.M * D.K) * D.C := by rw [D.M_K_comm]
      _ = D.K * D.C := by rw [← mul_assoc, D.M_sq, one_mul]
  calc
    (D.C * D.K - D.K * D.C) *
        ((1 : Module.End ℝ V) - D.M) =
        (D.C * D.K - D.K * D.C) -
          (D.C * D.K * D.M - D.K * D.C * D.M) := by
            noncomm_ring
    _ = 0 := by
      rw [D.cayley_hestenes_twisted, neg_mul, hMKCM, hKCM]
      module

end InfoGeometry.Canonical.CayleyHestenesGradedIntertwinerBridge

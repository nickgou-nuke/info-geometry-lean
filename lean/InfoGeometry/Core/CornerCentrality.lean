/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Group.Center
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Core.CornerCentrality

variable {A : Type*} [Ring A]

theorem unit_central_in_corner (P X : A) (hP : P * P = P) :
    P * (P * X * P) = (P * X * P) * P := by
  calc
    _ = (P * P) * X * P := by noncomm_ring
    _ = P * X * P := by rw [hP]
    _ = P * X * (P * P) := by rw [hP]
    _ = _ := by noncomm_ring

/-- No star or positivity assumption is needed when both transfer blocks vanish. -/
theorem commutes_iff_block_diagonal (P X : A) (hP : P * P = P) :
    P * X = X * P ↔ P * X * (1 - P) = 0 ∧ (1 - P) * X * P = 0 := by
  constructor
  · intro h
    constructor
    · calc
        _ = X * (P * (1 - P)) := by rw [h]; simp only [mul_assoc]
        _ = 0 := by simp [mul_sub, hP]
    · calc
        _ = (1 - P) * (P * X) := by rw [mul_assoc, ← h]
        _ = 0 := by rw [← mul_assoc]; simp [sub_mul, hP]
  · rintro ⟨h₁, h₂⟩
    have h₁' : P * X - P * X * P = 0 := by
      simpa only [mul_sub, mul_one] using h₁
    have h₂' : X * P - P * X * P = 0 := by
      simpa only [sub_mul, one_mul] using h₂
    exact (sub_eq_zero.mp h₁').trans (sub_eq_zero.mp h₂').symm

/-- Orthogonal corners commute, so one lies in the ambient centralizer of
the other. No commutativity of the ambient ring is assumed. -/
theorem orthogonal_corner_subset_centralizer (p q : A)
    (hpq : p * q = 0) (hqp : q * p = 0) :
    Set.range (fun x : A => q * x * q) ⊆
      Set.centralizer (Set.range (fun x : A => p * x * p)) := by
  rintro _ ⟨y, rfl⟩ _ ⟨x, rfl⟩
  have hleft : (p * x * p) * (q * y * q) = 0 := by
    calc
      _ = p * x * (p * q) * y * q := by simp only [mul_assoc]
      _ = 0 := by rw [hpq]; simp
  have hright : (q * y * q) * (p * x * p) = 0 := by
    calc
      _ = q * y * (q * p) * x * p := by simp only [mul_assoc]
      _ = 0 := by rw [hqp]; simp
  rw [hleft, hright]

/-- An orthogonal corner is strictly smaller than the full ambient
centralizer when the observed idempotent is nonzero. Its own unit witnesses
the missing centralizer element. This is not a statement about a left/right
regular representation on a different carrier. -/
theorem orthogonal_corner_ssubset_centralizer (p q : A)
    (hp : p * p = p) (hpq : p * q = 0) (hqp : q * p = 0) (hp0 : p ≠ 0) :
    Set.range (fun x : A => q * x * q) ⊂
      Set.centralizer (Set.range (fun x : A => p * x * p)) := by
  refine Set.ssubset_iff_subset_ne.mpr
    ⟨orthogonal_corner_subset_centralizer p q hpq hqp, ?_⟩
  intro heq
  have hpcentral : p ∈ Set.centralizer (Set.range (fun x : A => p * x * p)) := by
    rintro _ ⟨x, rfl⟩
    exact (unit_central_in_corner p x hp).symm
  rw [← heq] at hpcentral
  obtain ⟨x, hx⟩ := hpcentral
  have h := congrArg (fun z : A => p * z) hx
  have hzero : p * (q * x * q) = 0 := by
    simp only [← mul_assoc, hpq, zero_mul]
  rw [hzero, hp] at h
  exact hp0 h.symm

variable {R : Type*} [Ring R] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

theorem scalar_commutator (r : R) (P X : A) :
    (r • P) * X - X * (r • P) = r • (P * X - X * P) := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_sub]

theorem scalar_central_in_corner (r : R) (P X : A) (hP : P * P = P) :
    (r • P) * (P * X * P) = (P * X * P) * (r • P) := by
  simp only [smul_mul_assoc, mul_smul_comm, unit_central_in_corner P X hP]

end InfoGeometry.Core.CornerCentrality

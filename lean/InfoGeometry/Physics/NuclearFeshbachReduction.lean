/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic

/-!
# Exact Feshbach reduction at an arbitrary idempotent

The inverse acts on the complementary corner: its two products with the
denominator are `1 - P`, not the full identity. No finite dimension, inner
product, determinant, or diagonalizability is needed. The reduced eigenvalue
equation has the same spectral parameter as the supplied resolvent.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearFeshbachReduction

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The shifted complementary block, extended by zero on the model corner. -/
def denominator (P H : Module.End K V) (E : K) : Module.End K V :=
  E • (1 - P) - (1 - P) * H * (1 - P)

/-- The energy-dependent effective Hamiltonian, extended by zero off the model. -/
def effectiveHamiltonian (P H R : Module.End K V) : Module.End K V :=
  P * H * P + P * H * R * H * P

/-- Reconstruction from a model vector, with complementary response `R H P`. -/
def waveOperator (P H R : Module.End K V) : Module.End K V :=
  P + R * H * P

theorem projection_mul_resolvent_eq_zero (P R : Module.End K V)
    (hQR : (1 - P) * R = R) : P * R = 0 := by
  calc
    P * R = R - (1 - P) * R := by noncomm_ring
    _ = 0 := by rw [hQR, sub_self]

theorem resolvent_mul_projection_eq_zero (P R : Module.End K V)
    (hRQ : R * (1 - P) = R) : R * P = 0 := by
  calc
    R * P = R - R * (1 - P) := by noncomm_ring
    _ = 0 := by rw [hRQ, sub_self]

theorem projection_mul_waveOperator (P H R : Module.End K V)
    (hP : P * P = P) (hQR : (1 - P) * R = R) :
    P * waveOperator P H R = P := by
  have hPR := projection_mul_resolvent_eq_zero P R hQR
  simp only [waveOperator, mul_add, ← mul_assoc, hP, hPR, zero_mul, add_zero]

theorem waveOperator_mul_projection (P H R : Module.End K V)
    (hP : P * P = P) : waveOperator P H R * P = waveOperator P H R := by
  simp only [waveOperator, add_mul, mul_assoc, hP]

theorem effectiveHamiltonian_supported (P H R : Module.End K V)
    (hP : P * P = P) :
    P * effectiveHamiltonian P H R = effectiveHamiltonian P H R ∧
      effectiveHamiltonian P H R * P = effectiveHamiltonian P H R := by
  constructor
  · simp only [effectiveHamiltonian, mul_add, ← mul_assoc, hP]
  · simp only [effectiveHamiltonian, add_mul, mul_assoc, hP]

theorem complementary_column (P H R : Module.End K V) (E : K)
    (hQR : (1 - P) * R = R) (hDR : denominator P H E * R = 1 - P) :
    (1 - P) * H * R = E • R - (1 - P) := by
  have h : E • R - (1 - P) * H * R = 1 - P := by
    simpa only [denominator, sub_mul, smul_mul_assoc, mul_assoc, hQR] using hDR
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm

theorem complementary_row (P H R : Module.End K V) (E : K)
    (hRQ : R * (1 - P) = R) (hRD : R * denominator P H E = 1 - P) :
    R * H * (1 - P) = E • R - (1 - P) := by
  have h : E • R - R * H * (1 - P) = 1 - P := by
    simpa only [denominator, mul_sub, mul_smul_comm, ← mul_assoc, hRQ] using hRD
  apply eq_sub_iff_add_eq.mpr
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm

/-- The full residual of a reconstructed model state is exactly the reduced
residual. Only the right complementary inverse is needed in this direction. -/
theorem residual_identity (P H R : Module.End K V) (E : K)
    (hQR : (1 - P) * R = R) (hDR : denominator P H E * R = 1 - P) :
    H * waveOperator P H R - E • waveOperator P H R =
      effectiveHamiltonian P H R - E • P := by
  have hz : (1 - P) * H * R - E • R + (1 - P) = 0 := by
    rw [complementary_column P H R E hQR hDR]
    abel
  calc
    _ = (effectiveHamiltonian P H R - E • P) +
        ((1 - P) * H * R - E • R + (1 - P)) * H * P := by
      simp only [waveOperator, effectiveHamiltonian, smul_add,
        add_mul, sub_mul, smul_mul_assoc]
      noncomm_ring
    _ = _ := by rw [hz]; simp

/-- The left complementary inverse controls reconstruction of full solutions. -/
theorem reconstruction_identity (P H R : Module.End K V) (E : K)
    (hRQ : R * (1 - P) = R) (hRD : R * denominator P H E = 1 - P) :
    waveOperator P H R - 1 = R * (H - E • 1) := by
  calc
    waveOperator P H R - 1 =
        R * H - R * H * (1 - P) - (1 - P) := by
      unfold waveOperator
      noncomm_ring
    _ = R * H - (E • R - (1 - P)) - (1 - P) := by
      rw [complementary_row P H R E hRQ hRD]
    _ = R * (H - E • 1) := by
      simp only [mul_sub, mul_smul_comm, mul_one]
      abel

/-- Exact eigen-equation equivalence on the model subspace. -/
theorem eigen_equation_iff (P H R : Module.End K V) (E : K)
    (hQR : (1 - P) * R = R) (hDR : denominator P H E * R = 1 - P)
    (v : V) (hv : P v = v) :
    H (waveOperator P H R v) = E • waveOperator P H R v ↔
      effectiveHamiltonian P H R v = E • v := by
  have h := LinearMap.congr_fun (residual_identity P H R E hQR hDR) v
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hv] at h
  exact (sub_eq_zero.symm.trans (h ▸ sub_eq_zero))

/-- Every full eigenvector lies on the resolvent graph over its model part. -/
theorem reconstruct_eigenvector (P H R : Module.End K V) (E : K)
    (hP : P * P = P) (hRQ : R * (1 - P) = R)
    (hRD : R * denominator P H E = 1 - P)
    (ψ : V) (hψ : H ψ = E • ψ) : waveOperator P H R (P ψ) = ψ := by
  have h := LinearMap.congr_fun (reconstruction_identity P H R E hRQ hRD) ψ
  have hw : waveOperator P H R ψ = ψ := by
    simpa only [LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply,
      LinearMap.smul_apply, hψ, sub_self, map_zero, sub_eq_zero] using h
  calc
    waveOperator P H R (P ψ) = (waveOperator P H R * P) ψ := rfl
    _ = waveOperator P H R ψ := by rw [waveOperator_mul_projection P H R hP]
    _ = ψ := hw

/-- A nonzero full eigenvector cannot have zero model projection off the
complementary spectrum. This excludes losing an eigenvector in the reduction. -/
theorem projected_eigenvector_ne_zero (P H R : Module.End K V) (E : K)
    (hP : P * P = P) (hRQ : R * (1 - P) = R)
    (hRD : R * denominator P H E = 1 - P)
    (ψ : V) (hψ : H ψ = E • ψ) (hne : ψ ≠ 0) : P ψ ≠ 0 := by
  intro hz
  have h := reconstruct_eigenvector P H R E hP hRQ hRD ψ hψ
  rw [hz, map_zero] at h
  exact hne h.symm

/-- The reconstruction map is injective on model vectors, not on all of V. -/
theorem waveOperator_injective_on_model (P H R : Module.End K V)
    (hP : P * P = P) (hQR : (1 - P) * R = R)
    {v w : V} (hv : P v = v) (hw : P w = w)
    (h : waveOperator P H R v = waveOperator P H R w) : v = w := by
  have hPv := LinearMap.congr_fun (projection_mul_waveOperator P H R hP hQR) v
  have hPw := LinearMap.congr_fun (projection_mul_waveOperator P H R hP hQR) w
  change P (waveOperator P H R v) = P v at hPv
  change P (waveOperator P H R w) = P w at hPw
  rw [h, hPw, hv, hw] at hPv
  exact hPv.symm

end InfoGeometry.Physics.NuclearFeshbachReduction

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic
import InfoGeometry.Physics.NuclearOperatorSchurComplement
import InfoGeometry.Physics.SolovievFiniteSecularEigenproblem

/-!
# Exact Feshbach Reduction at an Arbitrary Idempotent and on a Direct Sum

1. **Idempotent-Projected Feshbach Reduction**:
   The inverse acts on the complementary corner: its two products with the
   denominator are `1 - P`, not the full identity. No finite dimension, inner
   product, determinant, or diagonalizability is needed. The reduced eigenvalue
   equation has the same spectral parameter as the supplied resolvent.

2. **Direct-Sum Block Feshbach Elimination**:
   The inverse belongs to the Q-space endomorphism `D − E`, not its singular
   zero extension to the ambient space. No existence of this inverse is asserted
   for the full phonon Hamiltonian. The theorem includes Q-space reconstruction.
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

variable {𝕜 P Q : Type*} [Field 𝕜]
  [AddCommGroup P] [Module 𝕜 P] [AddCommGroup Q] [Module 𝕜 Q]

/-- Native direct-sum block operator with independent P and Q dimensions. -/
def blockOperator (A : P →ₗ[𝕜] P) (B : Q →ₗ[𝕜] P)
    (C : P →ₗ[𝕜] Q) (D : Q →ₗ[𝕜] Q) : (P × Q) →ₗ[𝕜] (P × Q) :=
  (A.coprod B).prod (C.coprod D)

/-- Reconstruction at the chosen energy; K is the inverse of D−E. -/
def reconstruction (C : P →ₗ[𝕜] Q) (K : Q →ₗ[𝕜] Q) : P →ₗ[𝕜] (P × Q) :=
  LinearMap.id.prod (-(K.comp C))

theorem reconstruction_injective (C : P →ₗ[𝕜] Q) (K : Q →ₗ[𝕜] Q) :
    Function.Injective (reconstruction C K) := by
  intro x y h
  exact congrArg Prod.fst h

/-- Exact kernel equivalence on a direct sum, including the reconstructed complementary component. -/
theorem block_eigen_equation_iff
    (A : P →ₗ[𝕜] P) (B : Q →ₗ[𝕜] P) (C : P →ₗ[𝕜] Q) (D K : Q →ₗ[𝕜] Q)
    (E : 𝕜) (hK : NuclearOperatorSchurComplement.InversePair
      (D - E • LinearMap.id) K) (x : P) (y : Q) :
    blockOperator A B C D (x, y) = E • (x, y) ↔
      (A - B.comp (K.comp C)) x = E • x ∧ y = -K (C x) := by
  have hleft (z : Q) : K (D z - E • z) = z := by
    simpa using congrArg (fun T : Q →ₗ[𝕜] Q => T z) hK.left_inv
  have hright (z : Q) : D (K z) - E • K z = z := by
    simpa using congrArg (fun T : Q →ₗ[𝕜] Q => T z) hK.right_inv
  change (A x + B y, C x + D y) = (E • x, E • y) ↔ _
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨hp, hq⟩
    have hden : D y - E • y = -C x := by rw [← hq]; abel
    have hy : y = -K (C x) := by rw [← hleft y, hden, map_neg]
    refine ⟨?_, hy⟩
    simpa [hy, sub_eq_add_neg] using hp
  · rintro ⟨hp, rfl⟩
    constructor
    · simpa [sub_eq_add_neg] using hp
    · have h := hright (C x)
      simp only [map_neg, smul_neg]
      calc
        C x + -D (K (C x)) =
            (D (K (C x)) - E • K (C x)) + -D (K (C x)) :=
          congrArg (fun z => z + -D (K (C x))) h.symm
        _ = -(E • K (C x)) := by abel

/-- A reduced eigenvector reconstructs to a full one, with nonzero preserved. -/
theorem reconstructed_nonzero_eigenvector_iff
    (A : P →ₗ[𝕜] P) (B : Q →ₗ[𝕜] P) (C : P →ₗ[𝕜] Q) (D K : Q →ₗ[𝕜] Q)
    (E : 𝕜) (hK : NuclearOperatorSchurComplement.InversePair
      (D - E • LinearMap.id) K) (x : P) :
    (reconstruction C K x ≠ 0 ∧
      blockOperator A B C D (reconstruction C K x) = E • reconstruction C K x) ↔
    (x ≠ 0 ∧ (A - B.comp (K.comp C)) x = E • x) := by
  have hn : reconstruction C K x = 0 ↔ x = 0 :=
    (reconstruction_injective C K).eq_iff' (map_zero _)
  change (_ ∧ blockOperator A B C D (x, -K (C x)) = E • (x, -K (C x))) ↔ _
  rw [block_eigen_equation_iff A B C D K E hK]
  simp [hn]

/-- For a common carrier this is precisely the existing noncommutative Schur owner. -/
theorem effective_eq_existing (A B C K : P →ₗ[𝕜] P) :
    A - B.comp (K.comp C) =
      NuclearOperatorSchurComplement.effectiveOperator A B C K := by
  rfl

open InfoGeometry.Physics.SolovievFiniteSecularEigenproblem

/-- Concrete two-channel specialization: the complementary pole is explicitly excluded. -/
theorem two_channel_feshbach (a d v E : ℝ) (h : d - E ≠ 0) (ψ : Carrier) :
    isEigenpair (blockHamiltonian a d v) ψ E ↔
      (a - v ^ 2 / (d - E)) * ψ 0 = E * ψ 0 ∧
      ψ 1 = -(v * ψ 0) / (d - E) := by
  rw [block_eigenpair_iff]
  constructor
  · rintro ⟨hp, hq⟩
    have hy : ψ 1 = -(v * ψ 0) / (d - E) := by
      apply (eq_div_iff h).mpr
      nlinarith [hq]
    refine ⟨?_, hy⟩
    rw [hy] at hp
    field_simp at hp ⊢
    nlinarith [hp]
  · rintro ⟨hp, hy⟩
    have hq := (eq_div_iff h).mp hy
    constructor
    · rw [hy]
      field_simp [h] at hp ⊢
      nlinarith [hp]
    · nlinarith [hq]

/-- At an excluded Q-space pole a pure complementary eigenvector really exists.
The inverse hypothesis cannot be dropped even when the coupling vanishes. -/
theorem complementary_pole_eigenvector (a d : ℝ) :
    isEigenpair (blockHamiltonian a d 0) ![0, 1] d ∧
      (![0, 1] : Carrier) ≠ 0 := by
  constructor
  · rw [block_eigenpair_iff]
    simp
  · intro h
    have := congrFun h 1
    norm_num at this

end InfoGeometry.Physics.NuclearFeshbachReduction

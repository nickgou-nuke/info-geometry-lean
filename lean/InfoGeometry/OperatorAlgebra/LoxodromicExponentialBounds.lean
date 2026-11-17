/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.TripotentExponentialBounds
import InfoGeometry.OperatorAlgebra.QuadraticExponentialBounds

/-!
# Bounded orbits under commuting boost and rotary generators

The ambient real Banach algebra need not commute. Only the specified boost
and rotary generators commute. A uniformly bounded exponential factor cannot
remove an unbounded conjugation orbit of a commuting generator, because its
inverse is bounded by the same all-real-time bound.

For a tripotent `S`, an internal real complex structure `J`, and a nonzero
boost coefficient, this gives the full operator criterion: the loxodromic
orbit of `X` is bounded for all real times exactly when `S` commutes with `X`.
The observable need not commute with `J`. No finite-dimensional representation,
Hilbert adjoint, modular state, or irreversible semigroup is assumed.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.LoxodromicExponentialBounds

open InfoGeometry.Canonical
open InfoGeometry.OperatorAlgebra.ConservedOperatorFlow
open InfoGeometry.OperatorAlgebra.TripotentExponentialBounds
open InfoGeometry.OperatorAlgebra.QuadraticExponentialBounds

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

local instance : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℝ A

/-- Scalar multiplication of the generator reparametrizes the actual flow. -/
theorem expTransport_smul_generator (H X : A) (c t : ℝ) :
    expTransport (c • H) X t = expTransport H X (t * c) := by
  simp only [expTransport, smul_smul, smul_neg]

/-- Exponentials of the specified commuting generators factor, retaining
the noncommutative order of the observable and the inverse factors. -/
theorem expTransport_add_generator (H K X : A) (hHK : Commute H K) (t : ℝ) :
    expTransport (H + K) X t = expTransport H (expTransport K X t) t := by
  have hp : Commute (t • H) (t • K) := (hHK.smul_left t).smul_right t
  have hn : Commute (t • (-K)) (t • (-H)) :=
    ((hHK.symm.neg_left.neg_right).smul_left t).smul_right t
  have hneg : t • (-(H + K)) = t • (-K) + t • (-H) := by module
  simp only [expTransport]
  rw [smul_add, NormedSpace.exp_add_of_commute hp, hneg,
    NormedSpace.exp_add_of_commute hn]
  simp only [mul_assoc]

/-- Adding a central scalar generator leaves every conjugation orbit
unchanged. This is an identity of actual exponentials on the full algebra. -/
theorem expTransport_add_scalar_one (H X : A) (c t : ℝ) :
    expTransport (H + c • (1 : A)) X t = expTransport H X t := by
  rw [expTransport_add_generator H (c • (1 : A)) X
    ((Commute.one_right H).smul_right c) t]
  rw [(conserved_iff_commute (c • (1 : A)) X).mpr
    ((Commute.one_left X).smul_left c) t]

/-- A nonzero time rescaling preserves two-sided orbit boundedness. -/
theorem bounded_expTransport_smul_generator_iff
    (H X : A) (c : ℝ) (hc : c ≠ 0) :
    (∃ C : ℝ, ∀ t : ℝ, ‖expTransport (c • H) X t‖ ≤ C) ↔
      ∃ C : ℝ, ∀ t : ℝ, ‖expTransport H X t‖ ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun t => ?_⟩
    have ht := hC (t / c)
    rw [expTransport_smul_generator, div_mul_cancel₀ _ hc] at ht
    exact ht
  · rintro ⟨C, hC⟩
    refine ⟨C, fun t => ?_⟩
    rw [expTransport_smul_generator]
    exact hC (t * c)

private theorem norm_expTransport_le_of_exp_bound
    (K Y : A) (M : ℝ)
    (hM : ∀ t : ℝ, ‖NormedSpace.exp (t • K)‖ ≤ M) (t : ℝ) :
    ‖expTransport K Y t‖ ≤ M ^ 2 * ‖Y‖ := by
  have hMnonneg : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hneg : ‖NormedSpace.exp (t • (-K))‖ ≤ M := by
    simpa only [smul_neg, neg_smul] using hM (-t)
  calc
    ‖expTransport K Y t‖ ≤
        ‖NormedSpace.exp (t • K)‖ * ‖Y‖ *
          ‖NormedSpace.exp (t • (-K))‖ := by
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ M * ‖Y‖ * M := by gcongr; exact hM t
    _ = M ^ 2 * ‖Y‖ := by ring

/-- A commuting generator with a uniformly bounded two-sided exponential
cannot change which observables have bounded two-sided conjugation orbits. -/
theorem bounded_expTransport_add_iff_of_bounded_exp
    (H K X : A) (hHK : Commute H K)
    (hK : ∃ M : ℝ, ∀ t : ℝ, ‖NormedSpace.exp (t • K)‖ ≤ M) :
    (∃ C : ℝ, ∀ t : ℝ, ‖expTransport (H + K) X t‖ ≤ C) ↔
      ∃ C : ℝ, ∀ t : ℝ, ‖expTransport H X t‖ ≤ C := by
  rcases hK with ⟨M, hM⟩
  have hminus : ∀ t : ℝ, ‖NormedSpace.exp (t • (-K))‖ ≤ M := by
    intro t
    simpa only [smul_neg, neg_smul] using hM (-t)
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨M ^ 2 * C, fun t => ?_⟩
    have hcomm : Commute (-K) (H + K) :=
      (hHK.symm.neg_left).add_right ((Commute.refl K).neg_left)
    have hremove := expTransport_add_generator (-K) (H + K) X hcomm t
    have hsum : -K + (H + K) = H := by abel
    rw [hsum] at hremove
    rw [hremove]
    exact (norm_expTransport_le_of_exp_bound (-K) (expTransport (H + K) X t)
      M hminus t).trans (mul_le_mul_of_nonneg_left (hC t) (sq_nonneg M))
  · rintro ⟨C, hC⟩
    refine ⟨M ^ 2 * C, fun t => ?_⟩
    have hfactor := expTransport_add_generator K H X hHK.symm t
    rw [add_comm K H] at hfactor
    rw [hfactor]
    exact (norm_expTransport_le_of_exp_bound K (expTransport H X t) M hM t).trans
      (mul_le_mul_of_nonneg_left (hC t) (sq_nonneg M))

/-- A commuting internal real rotation does not regularize a nonzero boost
grade. The entire loxodromic conjugation orbit is bounded exactly on the
centralizer of the tripotent; no commutation of `X` with `J` is required. -/
theorem bounded_loxodromic_expTransport_iff
    (S J X : A) (hS : S * S * S = S) (hJ : J ^ 2 = -1)
    (hSJ : Commute S J) (γ ω : ℝ) (hγ : γ ≠ 0) :
    (∃ C : ℝ, ∀ t : ℝ, ‖expTransport (γ • S + ω • J) X t‖ ≤ C) ↔
      Commute S X := by
  have hrotation : ∃ M : ℝ, ∀ t : ℝ,
      ‖NormedSpace.exp (t • (ω • J))‖ ≤ M := by
    refine ⟨‖(1 : A)‖ + ‖J‖, fun t => ?_⟩
    simpa only [smul_smul, div_one] using
      norm_exp_le_of_sq_eq_neg_scalar J 1 (by norm_num)
        (by simpa using hJ) (t * ω)
  rw [bounded_expTransport_add_iff_of_bounded_exp (γ • S) (ω • J) X
    ((hSJ.smul_left γ).smul_right ω) hrotation,
    bounded_expTransport_smul_generator_iff S X γ hγ,
    bounded_expTransport_iff_commute hS X]

end InfoGeometry.OperatorAlgebra.LoxodromicExponentialBounds

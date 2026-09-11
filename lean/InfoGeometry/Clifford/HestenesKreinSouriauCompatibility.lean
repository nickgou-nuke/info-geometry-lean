import InfoGeometry.Clifford.ChiralGrandCanonicalHestenesRotor
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicRotor

/-!
# Hestenes--Krein--Souriau compatibility surface

This is a thin coherence owner.  The concrete Hestenes generators and rotors
remain owned by `ChiralGrandCanonicalHestenesRotor`; the commuting matrix
loxodromic model remains owned by `ChiralGrandCanonicalLoxodromicRotor`.  This
file exposes their separate elliptic/hyperbolic interpretations and the
anticommuting mixed-generator square for downstream Souriau consumers.
-/

noncomputable section

namespace InfoGeometry.Clifford.HestenesKreinSouriauCompatibility

open InfoGeometry.Clifford.ChiralGrandCanonicalLoxodromicRotor
open InfoGeometry.Clifford.ChiralGrandCanonicalHestenesRotor

theorem phaseAxis_elliptic_square :
    ChiralGrandCanonicalLoxodromicRotor.phaseAxis *
        ChiralGrandCanonicalLoxodromicRotor.phaseAxis =
      -(1 : ChiralGrandCanonicalLoxodromicRotor.Operator) :=
  ChiralGrandCanonicalLoxodromicRotor.phaseAxis_sq

theorem boostAxis_hyperbolic_square :
    ChiralGrandCanonicalLoxodromicRotor.boostAxis *
        ChiralGrandCanonicalLoxodromicRotor.boostAxis =
      (1 : ChiralGrandCanonicalLoxodromicRotor.Operator) :=
  ChiralGrandCanonicalLoxodromicRotor.boostAxis_sq

theorem elliptic_hyperbolic_commute :
    ChiralGrandCanonicalLoxodromicRotor.boostAxis *
        ChiralGrandCanonicalLoxodromicRotor.phaseAxis =
      ChiralGrandCanonicalLoxodromicRotor.phaseAxis *
        ChiralGrandCanonicalLoxodromicRotor.boostAxis :=
  ChiralGrandCanonicalLoxodromicRotor.boostAxis_phaseAxis_commute

theorem loxodromicRotor_factorization (eta theta : ℝ) :
    ChiralGrandCanonicalLoxodromicRotor.loxodromicRotor eta theta =
      ChiralGrandCanonicalLoxodromicRotor.boostRotor eta *
        ChiralGrandCanonicalLoxodromicRotor.phaseRotor theta :=
  rfl

theorem loxodromicRotor_inverse (eta theta : ℝ) :
    ChiralGrandCanonicalLoxodromicRotor.loxodromicRotor eta theta *
        ChiralGrandCanonicalLoxodromicRotor.loxodromicRotor (-eta) (-theta) =
      (1 : ChiralGrandCanonicalLoxodromicRotor.Operator) :=
  ChiralGrandCanonicalLoxodromicRotor.loxodromicRotor_mul_neg eta theta

theorem hestenes_boost_projector_weights (eta : ℝ) :
    Real.cosh eta + Real.sinh eta = Real.exp eta ∧
      Real.cosh eta - Real.sinh eta = Real.exp (-eta) :=
  ChiralGrandCanonicalHestenesRotor.boostRotor_projector_weights eta

theorem hestenes_phaseRotor_inverse (theta : ℝ) :
    ChiralGrandCanonicalHestenesRotor.phaseRotor theta *
        ChiralGrandCanonicalHestenesRotor.phaseRotor (-theta) =
      (1 : ChiralGrandCanonicalHestenesRotor.Operator) :=
  ChiralGrandCanonicalHestenesRotor.phaseRotor_mul_neg theta

theorem hestenes_boost_phase_generator_anticommute :
    InfoGeometry.Clifford.SplitQ11PhaseFlip.epsGen *
        InfoGeometry.Clifford.SplitQ11PhaseFlip.kGen +
        InfoGeometry.Clifford.SplitQ11PhaseFlip.kGen *
          InfoGeometry.Clifford.SplitQ11PhaseFlip.epsGen = 0 :=
  ChiralGrandCanonicalHestenesRotor.boost_phase_generators_anticommute

/-!
The concrete Hestenes elliptic and hyperbolic generators anticommute.  Thus
their mixed generator is governed by the split quadratic form on its two real
coefficients; no commuting-factorization claim is made here.
-/
theorem hestenes_mixed_generator_sq (theta eta : ℝ) :
    (theta • SplitQ11PhaseFlip.kGen + eta • SplitQ11PhaseFlip.epsGen) *
        (theta • SplitQ11PhaseFlip.kGen + eta • SplitQ11PhaseFlip.epsGen) =
      (eta ^ 2 - theta ^ 2) •
        (1 : ChiralGrandCanonicalHestenesRotor.Operator) := by
  rw [add_mul, mul_add]
  simp only [mul_add, smul_mul_assoc, mul_smul_comm]
  simp only [SplitQ11PhaseFlip.kGen_sq, SplitQ11Projectors.epsGen_sq]
  simp only [smul_smul]
  have hcoef : eta * theta = theta * eta := by ring
  rw [hcoef]
  rw [show
      (theta * theta) • (-1 : ChiralGrandCanonicalHestenesRotor.Operator) +
          (theta * eta) •
            (SplitQ11PhaseFlip.kGen * SplitQ11PhaseFlip.epsGen) +
          ((theta * eta) •
              (SplitQ11PhaseFlip.epsGen * SplitQ11PhaseFlip.kGen) +
            (eta * eta) • (1 : ChiralGrandCanonicalHestenesRotor.Operator)) =
        (theta * theta) • (-1 : ChiralGrandCanonicalHestenesRotor.Operator) +
          ((theta * eta) •
              (SplitQ11PhaseFlip.kGen * SplitQ11PhaseFlip.epsGen) +
            (theta * eta) •
              (SplitQ11PhaseFlip.epsGen * SplitQ11PhaseFlip.kGen)) +
          (eta * eta) • (1 : ChiralGrandCanonicalHestenesRotor.Operator) by
      ac_rfl]
  rw [← smul_add]
  rw [show SplitQ11PhaseFlip.kGen * SplitQ11PhaseFlip.epsGen +
      SplitQ11PhaseFlip.epsGen * SplitQ11PhaseFlip.kGen = 0 by
    simpa [add_comm] using hestenes_boost_phase_generator_anticommute]
  module

theorem hestenes_mixed_generator_sq_eq_zero (theta eta : ℝ)
    (h : eta ^ 2 = theta ^ 2) :
    (theta • SplitQ11PhaseFlip.kGen + eta • SplitQ11PhaseFlip.epsGen) *
        (theta • SplitQ11PhaseFlip.kGen + eta • SplitQ11PhaseFlip.epsGen) =
      (0 : ChiralGrandCanonicalHestenesRotor.Operator) := by
  rw [hestenes_mixed_generator_sq]
  rw [h]
  simp

/-! The coefficient plane has the expected hyperbolic/elliptic/null trichotomy. -/
theorem hestenes_mixed_generator_regime (theta eta : ℝ) :
    0 < eta ^ 2 - theta ^ 2 ∨
      eta ^ 2 - theta ^ 2 = 0 ∨
      eta ^ 2 - theta ^ 2 < 0 := by
  rcases lt_trichotomy (eta ^ 2 - theta ^ 2) 0 with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl h

theorem hestenes_mixed_generator_hyperbolic_scalar
    (theta eta : ℝ) (h : theta ^ 2 < eta ^ 2) :
    0 < eta ^ 2 - theta ^ 2 :=
  sub_pos.mpr h

theorem hestenes_mixed_generator_elliptic_scalar
    (theta eta : ℝ) (h : eta ^ 2 < theta ^ 2) :
    eta ^ 2 - theta ^ 2 < 0 :=
  sub_neg.mpr h

theorem hestenes_mixed_generator_even_pow (theta eta : ℝ) (n : ℕ) :
    (theta • SplitQ11PhaseFlip.kGen + eta • SplitQ11PhaseFlip.epsGen) ^ (2 * n) =
      ((eta ^ 2 - theta ^ 2) ^ n) •
        (1 : ChiralGrandCanonicalHestenesRotor.Operator) := by
  have hsq :
      (theta • SplitQ11PhaseFlip.kGen + eta • SplitQ11PhaseFlip.epsGen) ^ 2 =
        (eta ^ 2 - theta ^ 2) •
          (1 : ChiralGrandCanonicalHestenesRotor.Operator) := by
    rw [pow_two]
    exact hestenes_mixed_generator_sq theta eta
  have hmul (a b : ℝ) :
      (a • (1 : ChiralGrandCanonicalHestenesRotor.Operator)) *
          (b • (1 : ChiralGrandCanonicalHestenesRotor.Operator)) =
        (a * b) • (1 : ChiralGrandCanonicalHestenesRotor.Operator) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 1 <;> first | ring | simp
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ, pow_add, ih, hsq]
      rw [hmul]
      apply congrArg (fun r : ℝ => r •
        (1 : ChiralGrandCanonicalHestenesRotor.Operator))
      exact (pow_succ (eta ^ 2 - theta ^ 2) n).symm

theorem hestenes_mixed_generator_odd_pow (theta eta : ℝ) (n : ℕ) :
    (theta • SplitQ11PhaseFlip.kGen + eta • SplitQ11PhaseFlip.epsGen) ^ (2 * n + 1) =
      ((eta ^ 2 - theta ^ 2) ^ n) •
        (theta • SplitQ11PhaseFlip.kGen + eta • SplitQ11PhaseFlip.epsGen) := by
  rw [pow_add, hestenes_mixed_generator_even_pow]
  simp [smul_mul_assoc, mul_smul_comm]

end InfoGeometry.Clifford.HestenesKreinSouriauCompatibility

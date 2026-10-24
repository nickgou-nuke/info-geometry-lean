/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceRotor

/-!
# Rotor alternation and exact algebraic displacement identities

Adaptation of the supplied DeBruijnRotorAlternationCycle note. Names such as
"first derivative" in the source refer here to algebraic commutators, not a
proved differential equation. Squared displacement and sandwich identities
are not themselves a positive metric, distance, or probabilistic fidelity.
-/

namespace InfoGeometry.Canonical.DeBruijnRotorAlternationCycle

open InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Core.PeirceRotor
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra

variable {A : Type*} [Ring A] {d b : A}

/-- The pole starts moving unless the seed pair vanishes. -/
theorem wheel_polePlus (h : IsDualSeedPair d b) :
    wheelGenerator d b * polePlus d b - polePlus d b * wheelGenerator d b =
      -transitionVelocity d b := by
  change (d - b) * polePlus d b - polePlus d b * (d - b) = -(d + b)
  rw [sub_mul, mul_sub, h.dp, h.bp, h.pd, h.pb]
  abel

theorem wheel_poleMinus (h : IsDualSeedPair d b) :
    wheelGenerator d b * poleMinus d b - poleMinus d b * wheelGenerator d b =
      transitionVelocity d b := by
  change (d - b) * poleMinus d b - poleMinus d b * (d - b) = d + b
  rw [sub_mul, mul_sub, h.dq, h.bq, h.qd, h.qb]
  abel

/-- The active carrier is fixed while its two poles alternate. -/
theorem static_balance_commutes (h : IsDualSeedPair d b) :
    wheelGenerator d b * carrierSupport d b = carrierSupport d b * wheelGenerator d b := by
  apply sub_eq_zero.mp
  change _ * (polePlus d b + poleMinus d b) -
    (polePlus d b + poleMinus d b) * _ = 0
  calc
    _ = (wheelGenerator d b * polePlus d b - polePlus d b * wheelGenerator d b) +
        (wheelGenerator d b * poleMinus d b - poleMinus d b * wheelGenerator d b) := by
      noncomm_ring
    _ = 0 := by rw [wheel_polePlus h, wheel_poleMinus h, neg_add_cancel]

/-- First algebraic commutator in the polarization/velocity pair. -/
theorem first_derivative_polarization (h : IsDualSeedPair d b) :
    wheelGenerator d b * phasePolarization d b -
      phasePolarization d b * wheelGenerator d b = -(2 • transitionVelocity d b) := by
  change _ * (polePlus d b - poleMinus d b) -
    (polePlus d b - poleMinus d b) * _ = _
  calc
    _ = (wheelGenerator d b * polePlus d b - polePlus d b * wheelGenerator d b) -
        (wheelGenerator d b * poleMinus d b - poleMinus d b * wheelGenerator d b) := by
      noncomm_ring
    _ = _ := by rw [wheel_polePlus h, wheel_poleMinus h, two_nsmul]; abel

/-- The other commutator is an associative-ring identity with no seed hypothesis. -/
theorem second_derivative_restoring (d b : A) :
    wheelGenerator d b * transitionVelocity d b -
      transitionVelocity d b * wheelGenerator d b = 2 • phasePolarization d b := by
  change (d - b) * (d + b) - (d + b) * (d - b) = 2 • (d * b - b * d)
  rw [two_nsmul]
  noncomm_ring

/-- The double commutator is exactly minus four times the polarization. -/
theorem double_commutator_law (h : IsDualSeedPair d b) :
    wheelGenerator d b * (wheelGenerator d b * phasePolarization d b -
      phasePolarization d b * wheelGenerator d b) -
    (wheelGenerator d b * phasePolarization d b -
      phasePolarization d b * wheelGenerator d b) * wheelGenerator d b =
        -(4 • phasePolarization d b) := by
  rw [first_derivative_polarization h]
  calc
    _ = -(2 • (wheelGenerator d b * transitionVelocity d b -
      transitionVelocity d b * wheelGenerator d b)) := by
      simp only [two_nsmul]; noncomm_ring
    _ = _ := by rw [second_derivative_restoring]; simp only [smul_smul]; rfl

/-- Unlike a frequency argument, this equivalence does not cancel two or four. -/
theorem no_turning_iff_seeds_vanish (h : IsDualSeedPair d b) :
    wheelGenerator d b * polePlus d b - polePlus d b * wheelGenerator d b = 0 ↔
      d = 0 ∧ b = 0 := by
  rw [wheel_polePlus h, neg_eq_zero]
  exact h.velocity_eq_zero_iff

section Scalars

variable {R : Type*} [CommRing R] [Algebra R A]

/-- The source's chordal displacement direction. -/
def chordalDirection (c s : R) (d b : A) : A :=
  s • phasePolarization d b + c • transitionVelocity d b

/-- Its square is a scalar multiple of the active support. -/
theorem chordalDirection_sq (h : IsDualSeedPair d b) (c s : R) :
    chordalDirection c s d b * chordalDirection c s d b =
      (c * c + s * s) • carrierSupport d b := by
  unfold chordalDirection
  calc
    _ = (s * s) • (phasePolarization d b * phasePolarization d b) +
      (c * c) • (transitionVelocity d b * transitionVelocity d b) +
      (s * c) • (phasePolarization d b * transitionVelocity d b +
        transitionVelocity d b * phasePolarization d b) := by
      simp only [add_mul, mul_add, smul_mul_smul]
      module
    _ = _ := by rw [h.clifford_squares.2.2, h.clifford_squares.2.1,
      h.polarization_velocity]; module

/-- Exact displacement formula on the scalar unit circle. -/
theorem movingPolePlus_sub_polePlus {c s : R} (hcs : c * c + s * s = 1) :
    movingPolePlus c s d b - polePlus d b = -s • chordalDirection c s d b := by
  rw [movingPolePlus_formula]
  calc
    _ = (c * c + s * s - 1) • polePlus d b - s • chordalDirection c s d b := by
      unfold chordalDirection phasePolarization chiralSupport
      module
    _ = _ := by rw [hcs, sub_self, zero_smul, zero_sub, neg_smul]

/-- Algebraic chordal square; no norm or positivity structure is presupposed. -/
theorem chordal_square (h : IsDualSeedPair d b) {c s : R}
    (hcs : c * c + s * s = 1) :
    (movingPolePlus c s d b - polePlus d b) *
      (movingPolePlus c s d b - polePlus d b) = (s * s) • carrierSupport d b := by
  rw [movingPolePlus_sub_polePlus hcs, smul_mul_smul, chordalDirection_sq h, hcs,
    one_smul, neg_mul_neg]

/-- The reference/moving-pole commutator is a multiple of the skew generator. -/
theorem pole_moving_commutator (h : IsDualSeedPair d b) (c s : R) :
    polePlus d b * movingPolePlus c s d b - movingPolePlus c s d b * polePlus d b =
      -(c * s) • wheelGenerator d b := by
  rw [movingPolePlus_formula]
  change _ = -(c * s) • (d - b)
  simp only [transitionVelocity, majoranaPlus, mul_sub, sub_mul, mul_add, add_mul,
    mul_smul_comm, smul_mul_assoc, h.pp, h.pq, h.qp, h.pd, h.pb, h.dp, h.bp]
  module

/-- This commutator square does not require the unit-circle equation. -/
theorem commutator_square (h : IsDualSeedPair d b) (c s : R) :
    (polePlus d b * movingPolePlus c s d b - movingPolePlus c s d b * polePlus d b) *
      (polePlus d b * movingPolePlus c s d b - movingPolePlus c s d b * polePlus d b) =
      -((c * s) * (c * s)) • carrierSupport d b := by
  rw [pole_moving_commutator h, smul_mul_smul, h.clifford_squares.1]
  module

/-- Sandwich identity. A probabilistic interpretation requires extra hypotheses. -/
theorem transition_sandwich (h : IsDualSeedPair d b) (c s : R) :
    polePlus d b * movingPolePlus c s d b * polePlus d b = (c * c) • polePlus d b := by
  rw [movingPolePlus_formula]
  simp only [transitionVelocity, majoranaPlus, mul_sub, sub_mul, mul_add, add_mul,
    mul_smul_comm, smul_mul_assoc, h.pp, h.pq, h.qp, h.pd, h.pb, h.dp, h.bp,
    mul_zero, zero_mul, sub_zero, zero_add, add_zero, smul_zero]

/-- The three algebraic identities requested in the source, on one carrier. -/
theorem poincare_fubini_study_metric_master (h : IsDualSeedPair d b) {c s : R}
    (hcs : c * c + s * s = 1) :
    (movingPolePlus c s d b - polePlus d b) *
      (movingPolePlus c s d b - polePlus d b) = (s * s) • carrierSupport d b ∧
    (polePlus d b * movingPolePlus c s d b - movingPolePlus c s d b * polePlus d b) *
      (polePlus d b * movingPolePlus c s d b - movingPolePlus c s d b * polePlus d b) =
        -((c * s) * (c * s)) • carrierSupport d b ∧
    polePlus d b * movingPolePlus c s d b * polePlus d b = (c * c) • polePlus d b :=
  ⟨chordal_square h hcs, commutator_square h c s, transition_sandwich h c s⟩

end Scalars

end InfoGeometry.Canonical.DeBruijnRotorAlternationCycle

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.HyperbolicPeirceRotor
import InfoGeometry.Canonical.DeBruijnRotorAlternationCycle

/-!
# Hyperbolic--elliptic chordal duality, KMS diagonal decoherence, and bipartite sandwiches

This module connects the circular Peirce rotor (`phaseRotor c s d b`, `c^2 + s^2 = 1`)
and the hyperbolic squeeze rotor (`hyperbolicRotor u v d b`, `u^2 - v^2 = 1`) to:
1. Opposite-sign chordal displacement squares (`+s^2 • Delta` vs `-v^2 • Delta`),
2. Diagonal Peirce decoherence (`P_+ X P_+ + P_- X P_-`) recovering the KMS weight,
3. The Drazin vs. reflexive Moore--Penrose dichotomy on square-zero seeds (`d^2 = 0`),
4. Bipartite directed edge transport (`P_+ d P_- = d`, `P_- b P_+ = b`) and
   division-free two-state transition sandwiches (`P_+ Q_1 P_+(c, s)`).
-/

namespace InfoGeometry.Canonical.HyperbolicEllipticKmsBridge

open InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Core.PeirceRotor
open InfoGeometry.Core.HyperbolicPeirceRotor
open InfoGeometry.Canonical.DeBruijnRotorAlternationCycle
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra

variable {A : Type*} [Ring A] {d b : A}

/-- Any commuting generalized inverse (`x * d = d * x` and `d * x * d = d`) of a
square-zero element `d * d = 0` forces `d = 0`. Nonzero nilpotent seeds therefore
require noncommuting reflexive partners (`d * b ≠ b * d`). -/
theorem nilpotent_commuting_inverse_forces_zero (hd : d * d = 0) {x : A}
    (hcomm : d * x = x * d) (hrefl : d * x * d = d) : d = 0 := by
  calc
    d = (d * x) * d := hrefl.symm
    _ = (x * d) * d := by rw [hcomm]
    _ = x * (d * d) := by rw [mul_assoc]
    _ = 0 := by rw [hd, mul_zero]

/-- By contrast, the active carrier `Delta = d * b + b * d` is strictly idempotent
and is its own commuting group/Drazin inverse on the active subspace. -/
theorem carrierSupport_commuting_group_inverse (h : IsDualSeedPair d b) :
    carrierSupport d b * carrierSupport d b = carrierSupport d b ∧
    carrierSupport d b * carrierSupport d b * carrierSupport d b = carrierSupport d b := by
  have hidem : carrierSupport d b * carrierSupport d b = carrierSupport d b := by
    change (polePlus d b + poleMinus d b) * (polePlus d b + poleMinus d b) =
      polePlus d b + poleMinus d b
    simp only [add_mul, mul_add, h.pp, h.pq, h.qp, h.qq, add_zero, zero_add]
  exact ⟨hidem, by rw [hidem, hidem]⟩

/-- Bipartite directed edge transport between the white (`polePlus`) and black (`poleMinus`)
Peirce vertices: `d` maps `poleMinus` to `polePlus` while `b` maps `polePlus` to `poleMinus`. -/
theorem bipartite_directed_edge_transport (h : IsDualSeedPair d b) :
    polePlus d b * d * poleMinus d b = d ∧
    poleMinus d b * b * polePlus d b = b ∧
    poleMinus d b * d * polePlus d b = 0 ∧
    polePlus d b * b * poleMinus d b = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h.pd, h.dq]
  · rw [h.qb, h.bp]
  · rw [h.qd, zero_mul]
  · rw [h.pb, zero_mul]

/-- The polarization and wheel generators anticommute without dividing by two. -/
theorem polarization_wheel (h : IsDualSeedPair d b) :
    phasePolarization d b * wheelGenerator d b +
      wheelGenerator d b * phasePolarization d b = 0 := by
  change (polePlus d b - poleMinus d b) * (d - b) +
    (d - b) * (polePlus d b - poleMinus d b) = 0
  simp only [sub_mul, mul_sub, h.pd, h.pb, h.qd, h.qb, h.dp, h.bp, h.dq, h.bq]
  abel

/-- Hyperbolic boost commutator of `transitionVelocity` with `polePlus`. -/
theorem velocity_polePlus_commutator (h : IsDualSeedPair d b) :
    transitionVelocity d b * polePlus d b - polePlus d b * transitionVelocity d b =
      -wheelGenerator d b := by
  change (d + b) * polePlus d b - polePlus d b * (d + b) = -(d - b)
  rw [add_mul, mul_add, h.dp, h.bp, h.pd, h.pb]
  abel

/-- Refutation boundary: the hyperbolic boost commutator vanishes iff both seeds vanish. -/
theorem no_hyperbolic_boost_iff_seeds_vanish (h : IsDualSeedPair d b) :
    transitionVelocity d b * polePlus d b - polePlus d b * transitionVelocity d b = 0 ↔
      d = 0 ∧ b = 0 := by
  rw [velocity_polePlus_commutator h, neg_eq_zero]
  constructor
  · intro hJ
    have hp := congrArg (fun x : A => polePlus d b * x) hJ
    change polePlus d b * (d - b) = polePlus d b * 0 at hp
    have hd : d = 0 := by simpa only [mul_sub, h.pd, h.pb, sub_zero, mul_zero] using hp
    have hb : b = 0 := by
      have hdb : d - b = 0 := hJ
      rw [hd, zero_sub, neg_eq_zero] at hdb
      exact hdb
    exact ⟨hd, hb⟩
  · rintro ⟨rfl, rfl⟩
    exact sub_self 0

section Scalars

variable {R : Type*} [CommRing R] [Algebra R A]

/-- Hyperbolic chordal direction `v • Gamma - u • J`. -/
def hyperbolicChordalDirection (u v : R) (d b : A) : A :=
  v • phasePolarization d b - u • wheelGenerator d b

/-- Its square is `(v^2 - u^2) • carrierSupport d b`. -/
theorem hyperbolicChordalDirection_sq (h : IsDualSeedPair d b) (u v : R) :
    hyperbolicChordalDirection u v d b * hyperbolicChordalDirection u v d b =
      (v * v - u * u) • carrierSupport d b := by
  unfold hyperbolicChordalDirection
  calc
    _ = (v * v) • (phasePolarization d b * phasePolarization d b) +
        (u * u) • (wheelGenerator d b * wheelGenerator d b) -
        (v * u) • (phasePolarization d b * wheelGenerator d b +
          wheelGenerator d b * phasePolarization d b) := by
      simp only [sub_mul, mul_sub, smul_mul_smul]
      module
    _ = _ := by
      rw [h.clifford_squares.2.2, h.clifford_squares.1, polarization_wheel h]
      module

/-- Exact hyperbolic displacement on the scalar unit hyperbola `u^2 - v^2 = 1`. -/
theorem hyperbolicPolePlus_sub_polePlus {u v : R} (huv : u * u - v * v = 1) :
    hyperbolicPolePlus u v d b - polePlus d b = v • hyperbolicChordalDirection u v d b := by
  rw [hyperbolicPolePlus_formula]
  calc
    _ = (u * u - v * v - 1) • polePlus d b + v • hyperbolicChordalDirection u v d b := by
      unfold hyperbolicChordalDirection phasePolarization chiralSupport
      module
    _ = _ := by rw [huv, sub_self, zero_smul, zero_add]

/-- Opposite-sign (timelike) hyperbolic chordal square: `-(v * v) • carrierSupport d b`. -/
theorem hyperbolic_chordal_square (h : IsDualSeedPair d b) {u v : R}
    (huv : u * u - v * v = 1) :
    (hyperbolicPolePlus u v d b - polePlus d b) *
      (hyperbolicPolePlus u v d b - polePlus d b) = -((v * v) • carrierSupport d b) := by
  have hvu : v * v - u * u = -1 := by linear_combination -huv
  rw [hyperbolicPolePlus_sub_polePlus huv, smul_mul_smul, hyperbolicChordalDirection_sq h,
    hvu]
  module

/-- Hyperbolic transition sandwich: `P_+ * P_+^hyp(u, v) * P_+ = (u * u) • P_+`. -/
theorem hyperbolic_transition_sandwich (h : IsDualSeedPair d b) (u v : R) :
    polePlus d b * hyperbolicPolePlus u v d b * polePlus d b = (u * u) • polePlus d b := by
  rw [hyperbolicPolePlus_formula]
  simp only [wheelGenerator, majoranaMinus, mul_sub, sub_mul,
    mul_smul_comm, smul_mul_assoc, h.pp, h.pq, h.pd, h.pb, h.dp,
    sub_zero, smul_zero]

/-- Division-free two-state transition sandwich (Aharonov pre/post-selected amplitude)
of the transition velocity `Q_1 = d + b` between `polePlus` and `movingPolePlus c s`:
`P_+ * Q_1 * P_+(c, s) = (s * s) • d - (c * s) • P_+`. -/
theorem two_state_velocity_sandwich (h : IsDualSeedPair d b) (c s : R) :
    polePlus d b * transitionVelocity d b * movingPolePlus c s d b =
      (s * s) • d - (c * s) • polePlus d b := by
  have hPq : polePlus d b * transitionVelocity d b = d := by
    change polePlus d b * (d + b) = d
    rw [mul_add, h.pd, h.pb, add_zero]
  have hdb : d * b = polePlus d b := rfl
  rw [hPq, movingPolePlus_formula]
  simp only [transitionVelocity, majoranaPlus, mul_sub, mul_add, mul_smul_comm,
    h.dp, h.dq, h.d_sq, hdb, smul_zero, zero_add]

/-- Diagonal Peirce conditional expectation / decoherence `P_+ X P_+ + P_- X P_-`. -/
def diagonalDecoherence (d b X : A) : A :=
  polePlus d b * X * polePlus d b + poleMinus d b * X * poleMinus d b

/-- KMS modular weight `(u * u) • P_- + (v * v) • P_+`. -/
def kmsModularWeight (u v : R) (d b : A) : A :=
  (u * u) • poleMinus d b + (v * v) • polePlus d b

/-- Diagonal Peirce decoherence of `movingPolePlus c s d b` annihilates the off-diagonal
coherence `-c s • Q_1` and yields `kmsModularWeight s c d b`. -/
theorem diagonalDecoherence_movingPolePlus_eq_kms (h : IsDualSeedPair d b) (c s : R) :
    diagonalDecoherence d b (movingPolePlus c s d b) = kmsModularWeight s c d b := by
  unfold diagonalDecoherence kmsModularWeight
  rw [transition_sandwich h c s, movingPolePlus_formula]
  simp only [transitionVelocity, majoranaPlus, mul_sub, sub_mul, mul_add,
    mul_smul_comm, smul_mul_assoc, h.qp, h.qq, h.qd, h.qb, h.bq,
    sub_zero, zero_add, smul_zero]
  abel

/-- Master synthesis uniting elliptic vs. hyperbolic chordal squares and KMS decoherence. -/
theorem elliptic_hyperbolic_kms_master_synthesis (h : IsDualSeedPair d b)
    {c s u v : R} (hcs : c * c + s * s = 1) (huv : u * u - v * v = 1) :
    IsIdempotentElem (movingPolePlus c s d b) ∧
    IsIdempotentElem (hyperbolicPolePlus u v d b) ∧
    (movingPolePlus c s d b - polePlus d b) *
      (movingPolePlus c s d b - polePlus d b) = (s * s) • carrierSupport d b ∧
    (hyperbolicPolePlus u v d b - polePlus d b) *
      (hyperbolicPolePlus u v d b - polePlus d b) = -((v * v) • carrierSupport d b) ∧
    diagonalDecoherence d b (movingPolePlus c s d b) = kmsModularWeight s c d b :=
  ⟨(moving_projector_relations h hcs).1,
   (hyperbolic_projector_relations h huv).1,
   chordal_square h hcs,
   hyperbolic_chordal_square h huv,
   diagonalDecoherence_movingPolePlus_eq_kms h c s⟩

end Scalars

end InfoGeometry.Canonical.HyperbolicEllipticKmsBridge

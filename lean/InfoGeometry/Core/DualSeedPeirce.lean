/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DiracSuperalgebra

/-!
# Reflexive square-zero seeds on the existing Peirce carrier

The four input equations are weaker than a Moore--Penrose pair: no star is
required. Support and Majorana expressions are aliases of existing owners,
not new inverse or projection definitions. The MP adapter is one-way.
-/

namespace InfoGeometry.Core.DualSeedPeirce

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra

variable {A : Type*} [Ring A]

/-- The source's algebraic input: two square-zero reflexive partners. -/
structure IsDualSeedPair (d b : A) : Prop where
  d_sq : d * d = 0
  b_sq : b * b = 0
  inner : d * b * d = d
  outer : b * d * b = b

abbrev polePlus (d b : A) : A := exactSupport d b
abbrev poleMinus (d b : A) : A := coexactSupport d b
abbrev carrierSupport (d b : A) : A := activeSupport d b
abbrev zeroModeSupport (d b : A) : A := harmonicSupport d b
abbrev phasePolarization (d b : A) : A := chiralSupport d b
abbrev transitionVelocity (d b : A) : A := majoranaPlus d b
abbrev wheelGenerator (d b : A) : A := majoranaMinus d b

namespace IsDualSeedPair

variable {d b : A} (h : IsDualSeedPair d b)

/-- Swapping the two seeds reverses the poles. -/
theorem symm : IsDualSeedPair b d := ⟨h.b_sq, h.d_sq, h.outer, h.inner⟩

theorem pp : polePlus d b * polePlus d b = polePlus d b := by
  change (d * b) * (d * b) = d * b
  rw [← mul_assoc, h.inner]

theorem qq : poleMinus d b * poleMinus d b = poleMinus d b := h.symm.pp

theorem pq : polePlus d b * poleMinus d b = 0 := by
  change (d * b) * (b * d) = 0
  calc
    (d * b) * (b * d) = d * (b * b) * d := by simp only [mul_assoc]
    _ = 0 := by rw [h.b_sq, mul_zero, zero_mul]

theorem qp : poleMinus d b * polePlus d b = 0 := h.symm.pq

theorem pd : polePlus d b * d = d := h.inner

theorem dq : d * poleMinus d b = d := by
  change d * (b * d) = d
  rw [← mul_assoc, h.inner]

theorem dp : d * polePlus d b = 0 := by
  change d * (d * b) = 0
  rw [← mul_assoc, h.d_sq, zero_mul]

theorem qd : poleMinus d b * d = 0 := by
  change b * d * d = 0
  rw [mul_assoc, h.d_sq, mul_zero]

theorem qb : poleMinus d b * b = b := h.symm.pd

theorem bp : b * polePlus d b = b := h.symm.dq

theorem bq : b * poleMinus d b = 0 := h.symm.dp

theorem pb : polePlus d b * b = 0 := h.symm.qd

/-- Clifford squares on the active identity; these are not norm assertions. -/
theorem clifford_squares :
    wheelGenerator d b * wheelGenerator d b = -carrierSupport d b ∧
    transitionVelocity d b * transitionVelocity d b = carrierSupport d b ∧
    phasePolarization d b * phasePolarization d b = carrierSupport d b := by
  refine ⟨?_, ?_, ?_⟩
  · change (d - b) * (d - b) = -(d * b + b * d)
    noncomm_ring [h.d_sq, h.b_sq]
  · change (d + b) * (d + b) = d * b + b * d
    noncomm_ring [h.d_sq, h.b_sq]
  · change (polePlus d b - poleMinus d b) *
        (polePlus d b - poleMinus d b) = polePlus d b + poleMinus d b
    rw [sub_mul, mul_sub, mul_sub, h.pp, h.pq, h.qp, h.qq]
    abel

/-- The mixed Clifford anticommutator vanishes without dividing by two. -/
theorem polarization_velocity :
    phasePolarization d b * transitionVelocity d b +
      transitionVelocity d b * phasePolarization d b = 0 := by
  change (polePlus d b - poleMinus d b) * (d + b) +
    (d + b) * (polePlus d b - poleMinus d b) = 0
  simp only [sub_mul, mul_sub, add_mul, mul_add,
    h.pd, h.pb, h.qd, h.qb, h.dp, h.bp, h.dq, h.bq]
  abel

/-- No-turning criterion, valid also in characteristic two. -/
theorem velocity_eq_zero_iff : transitionVelocity d b = 0 ↔ d = 0 ∧ b = 0 := by
  constructor
  · intro hz
    have hp := congrArg (fun x : A => polePlus d b * x) hz
    change polePlus d b * (d + b) = polePlus d b * 0 at hp
    have hd : d = 0 := by simpa only [mul_add, h.pd, h.pb, add_zero, mul_zero] using hp
    have hb : b = 0 := by simpa [transitionVelocity, majoranaPlus, hd] using hz
    exact ⟨hd, hb⟩
  · rintro ⟨rfl, rfl⟩
    exact zero_add 0

end IsDualSeedPair

/-- Native MP input specializes to the weaker seed contract. -/
theorem dualSeedPair_of_mp [StarRing A] {d b : A}
    (h : IsMoorePenroseInverse d b) (hd : d * d = 0) : IsDualSeedPair d b :=
  ⟨hd, h.inverse_sq_eq_zero hd, h.aba_eq_a, h.bab_eq_b⟩

end InfoGeometry.Core.DualSeedPeirce

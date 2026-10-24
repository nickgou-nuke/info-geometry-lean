/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.DualSeedPeirce
import Mathlib.Tactic.Module

/-!
# Algebraic circle rotors and moving Peirce idempotents

Every calculation takes place in the original associative algebra. The four
scalar coordinates evaluate on its actual partial matrix units. No scalar
model substitutes for the operator carrier, and no metric is assumed.
-/

namespace InfoGeometry.Core.PeirceRotor

open InfoGeometry.Core.DualSeedPeirce
open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Evaluate four scalar coefficients on the actual Peirce matrix units. -/
def peirceBlock (d b : A) (a x y z : R) : A :=
  a • polePlus d b + x • d + y • b + z • poleMinus d b

variable {d b : A}

/-- Multiplication of supported operators, derived from the seed equations. -/
theorem peirceBlock_mul (h : IsDualSeedPair d b) (a x y z e f g k : R) :
    peirceBlock d b a x y z * peirceBlock d b e f g k =
      peirceBlock d b (a * e + x * g) (a * f + x * k)
        (y * e + z * g) (y * f + z * k) := by
  unfold peirceBlock
  simp only [add_mul, mul_add, smul_mul_smul, h.pp, h.pq, h.qp, h.qq,
    h.pd, h.pb, h.dp, h.dq, h.qd, h.qb, h.bp, h.bq, h.d_sq, h.b_sq, smul_zero]
  module

/-- The complementary idempotent annihilates every supported block. -/
theorem harmonic_block (h : IsDualSeedPair d b) (a x y z : R) :
    zeroModeSupport d b * peirceBlock d b a x y z = 0 ∧
    peirceBlock d b a x y z * zeroModeSupport d b = 0 := by
  change (1 - polePlus d b - poleMinus d b) * peirceBlock d b a x y z = 0 ∧
    peirceBlock d b a x y z * (1 - polePlus d b - poleMinus d b) = 0
  constructor <;> unfold peirceBlock <;>
    simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, h.pp, h.pq, h.qp, h.qq, h.pd, h.pb, h.dp, h.dq,
      h.qd, h.qb, h.bp, h.bq, smul_zero] <;> module

theorem harmonic_idempotent (h : IsDualSeedPair d b) :
    zeroModeSupport d b * zeroModeSupport d b = zeroModeSupport d b := by
  change (1 - polePlus d b - poleMinus d b) *
    (1 - polePlus d b - poleMinus d b) = 1 - polePlus d b - poleMinus d b
  simp only [sub_mul, mul_sub, one_mul, mul_one, h.pp, h.pq, h.qp, h.qq]
  abel

/-- Adjoin the identity on the harmonic complement. This is not an additive map. -/
def completedBlock (d b : A) (a x y z : R) : A :=
  zeroModeSupport d b + peirceBlock d b a x y z

theorem completedBlock_mul (h : IsDualSeedPair d b) (a x y z e f g k : R) :
    completedBlock d b a x y z * completedBlock d b e f g k =
      completedBlock d b (a * e + x * g) (a * f + x * k)
        (y * e + z * g) (y * f + z * k) := by
  simp only [completedBlock, add_mul, mul_add, harmonic_idempotent h,
    (harmonic_block h e f g k).1, (harmonic_block h a x y z).2,
    peirceBlock_mul h, add_zero, zero_add]

/-- The scalar circle rotor, equal to `P0 + c • Delta + s • J`. -/
def phaseRotor (c s : R) (d b : A) : A := completedBlock d b c s (-s) c

/-- This is the rotor specified in the attachment, on the existing carrier. -/
theorem phaseRotor_formula (c s : R) :
    phaseRotor c s d b = zeroModeSupport d b +
      c • carrierSupport d b + s • wheelGenerator d b := by
  unfold phaseRotor completedBlock peirceBlock carrierSupport activeSupport
    wheelGenerator majoranaMinus
  module

/-- The multiplication law holds before imposing a unit-circle constraint. -/
theorem phaseRotor_mul (h : IsDualSeedPair d b) (c s e f : R) :
    phaseRotor c s d b * phaseRotor e f d b =
      phaseRotor (c * e - s * f) (c * f + s * e) d b := by
  unfold phaseRotor
  rw [completedBlock_mul h]
  congr 1 <;> ring

/-- The identity rotor is the ambient identity, including on proper support. -/
theorem phaseRotor_one_zero : phaseRotor (1 : R) 0 d b = 1 := by
  simp only [phaseRotor, completedBlock, peirceBlock, neg_zero, one_smul,
    zero_smul, add_zero, zero_add]
  change (1 - polePlus d b - poleMinus d b) + (polePlus d b + poleMinus d b) = 1
  abel

/-- Both inverse equations use only the scalar circle equation. -/
theorem phaseRotor_inverse (h : IsDualSeedPair d b) {c s : R} (hcs : c * c + s * s = 1) :
    phaseRotor c s d b * phaseRotor c (-s) d b = 1 ∧
    phaseRotor c (-s) d b * phaseRotor c s d b = 1 := by
  have h₁ : c * c - s * (-s) = 1 := by simpa using hcs
  have h₂ : c * c - (-s) * s = 1 := by simpa using hcs
  constructor
  · rw [phaseRotor_mul h, h₁, show c * (-s) + s * c = 0 by ring]
    exact phaseRotor_one_zero
  · rw [phaseRotor_mul h, h₂, show c * s + (-s) * c = 0 by ring]
    exact phaseRotor_one_zero

/-- A native ambient unit; no inverse is left as an unproved field. -/
def phaseRotorUnit (h : IsDualSeedPair d b) {c s : R} (hcs : c * c + s * s = 1) : Aˣ where
  val := phaseRotor c s d b
  inv := phaseRotor c (-s) d b
  val_inv := (phaseRotor_inverse h hcs).1
  inv_val := (phaseRotor_inverse h hcs).2

/-- The moving positive pole, with the attachment's sign convention. -/
def movingPolePlus (c s : R) (d b : A) : A :=
  peirceBlock d b (c * c) (-(c * s)) (-(c * s)) (s * s)

/-- The complementary moving pole. -/
def movingPoleMinus (c s : R) (d b : A) : A :=
  peirceBlock d b (s * s) (c * s) (c * s) (c * c)

theorem movingPolePlus_formula (c s : R) :
    movingPolePlus c s d b = (c * c) • polePlus d b + (s * s) • poleMinus d b -
      (c * s) • transitionVelocity d b := by
  unfold movingPolePlus peirceBlock transitionVelocity majoranaPlus
  module

theorem movingPoleMinus_formula (c s : R) :
    movingPoleMinus c s d b = (s * s) • polePlus d b + (c * c) • poleMinus d b +
      (c * s) • transitionVelocity d b := by
  unfold movingPoleMinus peirceBlock transitionVelocity majoranaPlus
  module

/-- Conjugation computes the stated moving positive pole exactly. -/
theorem phaseRotor_conjugates_plus (h : IsDualSeedPair d b) (c s : R) :
    phaseRotor c s d b * polePlus d b * phaseRotor c (-s) d b =
      movingPolePlus c s d b := by
  have hp : polePlus d b = peirceBlock d b (1 : R) 0 0 0 := by simp [peirceBlock]
  rw [hp]
  unfold phaseRotor completedBlock
  rw [add_mul, (harmonic_block h (1 : R) 0 0 0).1, zero_add, peirceBlock_mul h,
    mul_add, (harmonic_block h _ _ _ _).2, zero_add, peirceBlock_mul h]
  unfold movingPolePlus
  congr 1 <;> ring

/-- Swapping the source pole gives the other moving idempotent. -/
theorem phaseRotor_conjugates_minus (h : IsDualSeedPair d b) (c s : R) :
    phaseRotor c s d b * poleMinus d b * phaseRotor c (-s) d b =
      movingPoleMinus c s d b := by
  have hq : poleMinus d b = peirceBlock d b (0 : R) 0 0 1 := by simp [peirceBlock]
  rw [hq]
  unfold phaseRotor completedBlock
  rw [add_mul, (harmonic_block h (0 : R) 0 0 1).1, zero_add, peirceBlock_mul h,
    mul_add, (harmonic_block h _ _ _ _).2, zero_add, peirceBlock_mul h]
  unfold movingPoleMinus
  congr 1 <;> ring

/-- Both idempotences and both annihilation orders follow from the same conjugation. -/
theorem moving_projector_relations (h : IsDualSeedPair d b) {c s : R} (hcs : c * c + s * s = 1) :
    IsIdempotentElem (movingPolePlus c s d b) ∧
    IsIdempotentElem (movingPoleMinus c s d b) ∧
    movingPolePlus c s d b * movingPoleMinus c s d b = 0 ∧
    movingPoleMinus c s d b * movingPolePlus c s d b = 0 := by
  have hi := (phaseRotor_inverse h hcs).2
  have transport (x y : A) :
      (phaseRotor c s d b * x * phaseRotor c (-s) d b) *
        (phaseRotor c s d b * y * phaseRotor c (-s) d b) =
      phaseRotor c s d b * (x * y) * phaseRotor c (-s) d b := by
    calc
      _ = phaseRotor c s d b * x *
          (phaseRotor c (-s) d b * phaseRotor c s d b) * y *
          phaseRotor c (-s) d b := by noncomm_ring
      _ = _ := by rw [hi]; simp only [mul_one, mul_assoc]
  change _ * _ = _ ∧ _ * _ = _ ∧ _ ∧ _
  rw [← phaseRotor_conjugates_plus h, ← phaseRotor_conjugates_minus h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [transport, h.pp]
  · rw [transport, h.qq]
  · rw [transport, h.pq, mul_zero, zero_mul]
  · rw [transport, h.qp, mul_zero, zero_mul]

/-- The two moving poles partition the same active support. -/
theorem moving_poles_sum {c s : R} (hcs : c * c + s * s = 1) :
    movingPolePlus c s d b + movingPoleMinus c s d b = carrierSupport d b := by
  rw [movingPolePlus_formula, movingPoleMinus_formula]
  calc
    _ = (c * c + s * s) • (polePlus d b + poleMinus d b) := by module
    _ = carrierSupport d b := by simpa only [hcs, one_smul]

end InfoGeometry.Core.PeirceRotor

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Orthogonal.O55ContactCarrier
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.OfAssociative

/-! Native orthogonal endomorphism lane over the `(5,5)` contact carrier. -/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

attribute [local instance 100] LieRing.ofAssociativeRing

abbrev End55 := Module.End ℝ Vector55

def IsSplitSkew (A : End55) : Prop :=
  ∀ x y, splitPairing (A x) y + splitPairing x (A y) = 0

@[simp] theorem isSplitSkew_zero : IsSplitSkew (0 : End55) := by
  intro x y
  simp

theorem isSplitSkew_add {A B : End55}
    (hA : IsSplitSkew A) (hB : IsSplitSkew B) :
    IsSplitSkew (A + B) := by
  intro x y
  simp only [LinearMap.add_apply, splitPairing_add_left,
    splitPairing_add_right]
  linarith [hA x y, hB x y]

theorem isSplitSkew_smul {A : End55} (hA : IsSplitSkew A) (c : ℝ) :
    IsSplitSkew (c • A) := by
  intro x y
  simp only [LinearMap.smul_apply, splitPairing_smul_left,
    splitPairing_smul_right]
  calc
    c * splitPairing (A x) y + c * splitPairing x (A y) =
        c * (splitPairing (A x) y + splitPairing x (A y)) := by ring
    _ = c * 0 := by rw [hA x y]
    _ = 0 := by ring

theorem isSplitSkew_commutator {A B : End55}
    (hA : IsSplitSkew A) (hB : IsSplitSkew B) :
    IsSplitSkew ⁅A, B⁆ := by
  change IsSplitSkew (A * B - B * A)
  intro x y
  have hAB := hA (B x) y
  have hBA := hB (A x) y
  have hAy := hA x (B y)
  have hBy := hB x (A y)
  change splitPairing (A (B x) - B (A x)) y +
      splitPairing x (A (B y) - B (A y)) = 0
  rw [splitPairing_sub_left, splitPairing_sub_right]
  linarith

def splitOrthogonalLie : LieSubalgebra ℝ End55 where
  carrier := {A | IsSplitSkew A}
  zero_mem' := isSplitSkew_zero
  add_mem' := fun hA hB => isSplitSkew_add hA hB
  smul_mem' := by
    intro c A hA
    exact isSplitSkew_smul hA c
  lie_mem' := fun hA hB => isSplitSkew_commutator hA hB

abbrev O55Lie := splitOrthogonalLie

def contactEulerEnd : End55 where
  toFun x i := contactWeightR i * x i
  map_add' x y := by
    ext i
    simp [mul_add]
  map_smul' c x := by
    ext i
    simp [contactWeightR]
    ring

@[simp] theorem contactEulerEnd_apply (x : Vector55) (i : Fin 10) :
    contactEulerEnd x i = contactWeightR i * x i := rfl

theorem contactEuler_isSplitSkew : IsSplitSkew contactEulerEnd := by
  intro x y
  simp [splitPairing, contactEulerEnd, contactWeightR, contactWeight]
  ring

def contactEuler : O55Lie :=
  ⟨contactEulerEnd, contactEuler_isSplitSkew⟩

@[simp] theorem contactEuler_mem :
    (contactEuler : End55) = contactEulerEnd := rfl

private lemma contactWeightR_cube (i : Fin 10) :
    contactWeightR i ^ 3 = contactWeightR i := by
  fin_cases i <;> norm_num [contactWeightR, contactWeight]

theorem contactEuler_cube :
    contactEulerEnd * contactEulerEnd * contactEulerEnd = contactEulerEnd := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [Module.End.mul_apply, contactEulerEnd_apply]
  calc
    contactWeightR i * (contactWeightR i * (contactWeightR i * x i)) =
        contactWeightR i ^ 3 * x i := by ring
    _ = contactWeightR i * x i := by rw [contactWeightR_cube]


/-- The crosscap endomorphism reverses the ten coordinate directions. -/
def crosscapEnd : End55 where
  toFun x i := x (dualIndex i)
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

@[simp] theorem crosscapEnd_apply (x : Vector55) (i : Fin 10) :
    crosscapEnd x i = x (dualIndex i) := rfl

theorem crosscapEnd_sq : crosscapEnd * crosscapEnd = (1 : End55) := by
  apply LinearMap.ext
  intro x; funext i
  simp [Module.End.mul_apply]

@[simp] theorem crosscapEnd_apply_twice (x : Vector55) :
    crosscapEnd (crosscapEnd x) = x := by
  simpa [Module.End.mul_apply] using LinearMap.congr_fun crosscapEnd_sq x

theorem crosscapEnd_isometry (x y : Vector55) :
    splitPairing (crosscapEnd x) (crosscapEnd y) = splitPairing x y := by
  simp [splitPairing, crosscapEnd, dualIndex]
  ring

theorem crosscapEnd_pairing_move (x y : Vector55) :
    splitPairing (crosscapEnd x) y = splitPairing x (crosscapEnd y) := by
  calc
    splitPairing (crosscapEnd x) y =
        splitPairing (crosscapEnd x) (crosscapEnd (crosscapEnd y)) := by
          rw [crosscapEnd_apply_twice]
    _ = splitPairing x (crosscapEnd y) :=
      crosscapEnd_isometry x (crosscapEnd y)

theorem crosscap_conjugates_euler :
    crosscapEnd * contactEulerEnd * crosscapEnd = -contactEulerEnd := by
  apply LinearMap.ext
  intro x; funext i
  simp [Module.End.mul_apply, contactEulerEnd_apply, contactWeightR_dualIndex]

theorem crosscap_anticommutes_euler :
    contactEulerEnd * crosscapEnd = -(crosscapEnd * contactEulerEnd) := by
  apply LinearMap.ext
  intro x; funext i
  simp [Module.End.mul_apply, contactEulerEnd_apply, contactWeightR_dualIndex]

theorem crosscap_conjugate_isSplitSkew {A : End55} (hA : IsSplitSkew A) :
    IsSplitSkew (crosscapEnd * A * crosscapEnd) := by
  intro x y
  change splitPairing (crosscapEnd (A (crosscapEnd x))) y +
      splitPairing x (crosscapEnd (A (crosscapEnd y))) = 0
  rw [crosscapEnd_pairing_move (A (crosscapEnd x)) y,
    ← crosscapEnd_pairing_move x (A (crosscapEnd y))]
  exact hA (crosscapEnd x) (crosscapEnd y)

def crosscapConjugation : Module.End ℝ O55Lie where
  toFun A :=
    ⟨crosscapEnd * (A : End55) * crosscapEnd,
      crosscap_conjugate_isSplitSkew A.property⟩
  map_add' A B := by
    apply Subtype.ext; simp [mul_add, add_mul]
  map_smul' c A := by
    apply Subtype.ext; simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

theorem crosscapConjugation_sq :
    crosscapConjugation * crosscapConjugation = (1 : Module.End ℝ O55Lie) := by
  apply LinearMap.ext
  intro A; apply Subtype.ext
  change crosscapEnd * (crosscapEnd * (A : End55) * crosscapEnd) * crosscapEnd = (A : End55)
  calc
    crosscapEnd * (crosscapEnd * (A : End55) * crosscapEnd) * crosscapEnd =
        (crosscapEnd * crosscapEnd) * A * (crosscapEnd * crosscapEnd) := by noncomm_ring
    _ = A := by rw [crosscapEnd_sq]; simp

theorem crosscapConjugation_bracket (A B : O55Lie) :
    crosscapConjugation ⁅A, B⁆ =
      ⁅crosscapConjugation A, crosscapConjugation B⁆ := by
  apply Subtype.ext
  change crosscapEnd * ((A : End55) * B - B * A) * crosscapEnd =
    (crosscapEnd * A * crosscapEnd) * (crosscapEnd * B * crosscapEnd) -
      (crosscapEnd * B * crosscapEnd) * (crosscapEnd * A * crosscapEnd)
  have hAB :
      (crosscapEnd * (A : End55) * crosscapEnd) *
          (crosscapEnd * B * crosscapEnd) =
        crosscapEnd * A * B * crosscapEnd := by
    calc
      (crosscapEnd * (A : End55) * crosscapEnd) *
          (crosscapEnd * B * crosscapEnd) =
        crosscapEnd * A * (crosscapEnd * crosscapEnd) * B * crosscapEnd := by
          noncomm_ring
      _ = crosscapEnd * A * B * crosscapEnd := by
          rw [crosscapEnd_sq]; simp
  have hBA :
      (crosscapEnd * (B : End55) * crosscapEnd) *
          (crosscapEnd * A * crosscapEnd) =
        crosscapEnd * B * A * crosscapEnd := by
    calc
      (crosscapEnd * (B : End55) * crosscapEnd) *
          (crosscapEnd * A * crosscapEnd) =
        crosscapEnd * B * (crosscapEnd * crosscapEnd) * A * crosscapEnd := by
          noncomm_ring
      _ = crosscapEnd * B * A * crosscapEnd := by
          rw [crosscapEnd_sq]; simp
  rw [hAB, hBA]
  rw [mul_sub, sub_mul]
  noncomm_ring

end InfoGeometry.Orthogonal.O55Contact

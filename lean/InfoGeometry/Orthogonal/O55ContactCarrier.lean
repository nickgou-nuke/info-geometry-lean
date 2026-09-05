import Mathlib

/-!
# A concrete split `(5,5)` orthogonal carrier

The ten-dimensional real carrier is written in coordinates adapted to a
`2 + 6 + 2` contact decomposition.  The first and last two coordinates form
two hyperbolic pairs; the middle six carry a diagonal `(3,3)` form.
Infinitesimal isometries are packaged as a native `LieSubalgebra` of the
associative endomorphism algebra.
-/

noncomputable section

namespace InfoGeometry.Orthogonal.O55Contact

abbrev Vector55 := Fin 10 → ℝ
abbrev End55 := Module.End ℝ Vector55

def dualIndex : Fin 10 → Fin 10 :=
  ![(8 : Fin 10), 9, 2, 3, 4, 5, 6, 7, 0, 1]

def contactWeight : Fin 10 → ℤ :=
  ![(-1 : ℤ), -1, 0, 0, 0, 0, 0, 0, 1, 1]

def contactWeightR (i : Fin 10) : ℝ := (contactWeight i : ℝ)

@[simp] theorem dualIndex_involutive (i : Fin 10) :
    dualIndex (dualIndex i) = i := by
  fin_cases i <;> rfl

@[simp] theorem contactWeight_dualIndex (i : Fin 10) :
    contactWeight (dualIndex i) = -contactWeight i := by
  fin_cases i <;> rfl

@[simp] theorem contactWeightR_dualIndex (i : Fin 10) :
    contactWeightR (dualIndex i) = -contactWeightR i := by
  simp [contactWeightR]

/-- Symmetric form with two hyperbolic pairs and a middle `(3,3)` block. -/
def splitPairing (x y : Vector55) : ℝ :=
  x 0 * y 8 + x 1 * y 9 + x 8 * y 0 + x 9 * y 1 +
  x 2 * y 2 + x 3 * y 3 + x 4 * y 4 -
  x 5 * y 5 - x 6 * y 6 - x 7 * y 7

@[simp] theorem splitPairing_zero_left (y : Vector55) :
    splitPairing 0 y = 0 := by simp [splitPairing]

@[simp] theorem splitPairing_zero_right (x : Vector55) :
    splitPairing x 0 = 0 := by simp [splitPairing]

@[simp] theorem splitPairing_add_left (x y z : Vector55) :
    splitPairing (x + y) z = splitPairing x z + splitPairing y z := by
  simp [splitPairing]
  ring

@[simp] theorem splitPairing_add_right (x y z : Vector55) :
    splitPairing x (y + z) = splitPairing x y + splitPairing x z := by
  simp [splitPairing]
  ring

@[simp] theorem splitPairing_neg_left (x y : Vector55) :
    splitPairing (-x) y = -splitPairing x y := by
  simp [splitPairing]
  ring

@[simp] theorem splitPairing_neg_right (x y : Vector55) :
    splitPairing x (-y) = -splitPairing x y := by
  simp [splitPairing]
  ring

@[simp] theorem splitPairing_sub_left (x y z : Vector55) :
    splitPairing (x - y) z = splitPairing x z - splitPairing y z := by
  simp [sub_eq_add_neg]

@[simp] theorem splitPairing_sub_right (x y z : Vector55) :
    splitPairing x (y - z) = splitPairing x y - splitPairing x z := by
  simp [sub_eq_add_neg]

@[simp] theorem splitPairing_smul_left (c : ℝ) (x y : Vector55) :
    splitPairing (c • x) y = c * splitPairing x y := by
  simp [splitPairing]
  ring

@[simp] theorem splitPairing_smul_right (c : ℝ) (x y : Vector55) :
    splitPairing x (c • y) = c * splitPairing x y := by
  simp [splitPairing]
  ring

theorem splitPairing_comm (x y : Vector55) :
    splitPairing x y = splitPairing y x := by
  simp [splitPairing]
  ring

def coordinateVector (i : Fin 10) : Vector55 :=
  fun j => if j = i then 1 else 0

@[simp] theorem splitPairing_coordinate_right (x : Vector55) (i : Fin 10) :
    splitPairing x (coordinateVector (dualIndex i)) =
      (if i = 5 ∨ i = 6 ∨ i = 7 then -x i else x i) := by
  fin_cases i <;> simp [splitPairing, coordinateVector, dualIndex]

theorem splitPairing_nondegenerate_left (x : Vector55)
    (h : ∀ y, splitPairing x y = 0) : x = 0 := by
  funext i
  have hi := h (coordinateVector (dualIndex i))
  rw [splitPairing_coordinate_right] at hi
  fin_cases i <;> simpa using hi

theorem splitPairing_nondegenerate_right (y : Vector55)
    (h : ∀ x, splitPairing x y = 0) : y = 0 := by
  apply splitPairing_nondegenerate_left y
  intro x
  rw [splitPairing_comm]
  exact h x

def positiveOuter (i : Fin 2) : Vector55 :=
  coordinateVector ⟨i.val, by omega⟩ +
    coordinateVector ⟨i.val + 8, by omega⟩

def negativeOuter (i : Fin 2) : Vector55 :=
  coordinateVector ⟨i.val, by omega⟩ -
    coordinateVector ⟨i.val + 8, by omega⟩

def positiveMiddle (i : Fin 3) : Vector55 :=
  coordinateVector ⟨i.val + 2, by omega⟩

def negativeMiddle (i : Fin 3) : Vector55 :=
  coordinateVector ⟨i.val + 5, by omega⟩

@[simp] theorem positiveOuter_norm (i : Fin 2) :
    splitPairing (positiveOuter i) (positiveOuter i) = 2 := by
  fin_cases i <;> norm_num [positiveOuter, splitPairing, coordinateVector]

@[simp] theorem negativeOuter_norm (i : Fin 2) :
    splitPairing (negativeOuter i) (negativeOuter i) = -2 := by
  fin_cases i <;> norm_num [negativeOuter, splitPairing, coordinateVector]

@[simp] theorem positiveMiddle_norm (i : Fin 3) :
    splitPairing (positiveMiddle i) (positiveMiddle i) = 1 := by
  fin_cases i <;> norm_num [positiveMiddle, splitPairing, coordinateVector]

@[simp] theorem negativeMiddle_norm (i : Fin 3) :
    splitPairing (negativeMiddle i) (negativeMiddle i) = -1 := by
  fin_cases i <;> norm_num [negativeMiddle, splitPairing, coordinateVector]

theorem split_signature_five_five_certificate :
    (∀ i : Fin 2, 0 < splitPairing (positiveOuter i) (positiveOuter i)) ∧
      (∀ i : Fin 3, 0 < splitPairing (positiveMiddle i) (positiveMiddle i)) ∧
      (∀ i : Fin 2, splitPairing (negativeOuter i) (negativeOuter i) < 0) ∧
      (∀ i : Fin 3, splitPairing (negativeMiddle i) (negativeMiddle i) < 0) := by
  exact ⟨fun i => by simp, fun i => by simp,
    fun i => by simp, fun i => by simp⟩

def IsSplitSkew (A : End55) : Prop :=
  ∀ x y, splitPairing (A x) y + splitPairing x (A y) = 0

@[simp] theorem isSplitSkew_zero : IsSplitSkew (0 : End55) := by
  intro x y
  simp [IsSplitSkew]

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
  rw [hA x y]
  ring

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
  smul_mem' := fun c A hA => isSplitSkew_smul hA c
  lie_mem' := fun A B hA hB => isSplitSkew_commutator hA hB

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

theorem contactEuler_cube :
    contactEulerEnd * contactEulerEnd * contactEulerEnd = contactEulerEnd := by
  apply LinearMap.ext
  intro x
  funext i
  fin_cases i <;>
    simp [Module.End.mul_apply, contactEulerEnd, contactWeightR,
      contactWeight]

def crosscapEnd : End55 where
  toFun x i := x (dualIndex i)
  map_add' x y := by
    ext i
    simp
  map_smul' c x := by
    ext i
    simp

@[simp] theorem crosscapEnd_apply (x : Vector55) (i : Fin 10) :
    crosscapEnd x i = x (dualIndex i) := rfl

theorem crosscapEnd_sq :
    crosscapEnd * crosscapEnd = (1 : End55) := by
  apply LinearMap.ext
  intro x
  funext i
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
  intro x
  funext i
  simp [Module.End.mul_apply, contactEulerEnd_apply,
    contactWeightR_dualIndex]

theorem crosscap_anticommutes_euler :
    contactEulerEnd * crosscapEnd = -(crosscapEnd * contactEulerEnd) := by
  apply LinearMap.ext
  intro x
  funext i
  simp [Module.End.mul_apply, contactEulerEnd_apply,
    contactWeightR_dualIndex]

theorem crosscap_conjugate_isSplitSkew {A : End55}
    (hA : IsSplitSkew A) :
    IsSplitSkew (crosscapEnd * A * crosscapEnd) := by
  intro x y
  change splitPairing (crosscapEnd (A (crosscapEnd x))) y +
      splitPairing x (crosscapEnd (A (crosscapEnd y))) = 0
  rw [crosscapEnd_pairing_move]
  rw [← crosscapEnd_pairing_move]
  exact hA (crosscapEnd x) (crosscapEnd y)

def crosscapConjugation : Module.End ℝ O55Lie where
  toFun A :=
    ⟨crosscapEnd * (A : End55) * crosscapEnd,
      crosscap_conjugate_isSplitSkew A.property⟩
  map_add' A B := by
    apply Subtype.ext
    simp [mul_add, add_mul]
  map_smul' c A := by
    apply Subtype.ext
    simp [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

theorem crosscapConjugation_sq :
    crosscapConjugation * crosscapConjugation =
      (1 : Module.End ℝ O55Lie) := by
  apply LinearMap.ext
  intro A
  apply Subtype.ext
  change crosscapEnd * (crosscapEnd * (A : End55) * crosscapEnd) *
      crosscapEnd = (A : End55)
  noncomm_ring [crosscapEnd_sq]

theorem crosscapConjugation_bracket (A B : O55Lie) :
    crosscapConjugation ⁅A, B⁆ =
      ⁅crosscapConjugation A, crosscapConjugation B⁆ := by
  apply Subtype.ext
  change crosscapEnd * ((A : End55) * B - B * A) * crosscapEnd =
    (crosscapEnd * A * crosscapEnd) *
        (crosscapEnd * B * crosscapEnd) -
      (crosscapEnd * B * crosscapEnd) *
        (crosscapEnd * A * crosscapEnd)
  noncomm_ring [crosscapEnd_sq]

theorem carrier_and_generator_counts :
    Fintype.card (Fin 10) = 10 ∧ Nat.choose 10 2 = 45 := by
  norm_num [Nat.choose]

end InfoGeometry.Orthogonal.O55Contact

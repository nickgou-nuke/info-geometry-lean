import Mathlib.Tactic

/-!
# Finite `Pin(5,5)` reflection/glide socket

This module proves the finite split-signature reflection/glide identities used
by the `Pin(5,5)` interpretation.

The carrier is the explicit split vector space `R^5 ⊕ R^5` with hyperbolic
pairing

`<p,w>,<p',w'> = p·w' + w·p'`.

We prove:

* the first-pair sign reflection preserves the split `O(5,5)` pairing;
* the reflection is involutive;
* a glide obtained by composing that reflection with a half-translation along
  an invariant coordinate squares to a unit translation.

#### BUCKET 1: CLOSED FINITE THEOREMS

`pinReflection_preserves_splitPair`, `pinReflection_involutive`,
`translateP_add`, and `glide_square_eq_translation`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

This is not a full Clifford algebra model of `Pin(5,5)`, a proof of the double
cover map `Pin(5,5) -> O(5,5)`, or a theorem about physical spacetime.  Those
require a full Clifford representation and sandwich-action formalization.
-/

noncomputable section

namespace InfoGeometry.Clifford.Pin55ReflectionGlide

/-- Split `5+5` real carrier, written as momentum/winding coordinates. -/
@[ext]
structure Split55 where
  p : Fin 5 → ℝ
  w : Fin 5 → ℝ

/-- Concrete instantiation of the split 55 structure. -/
instance : Inhabited Split55 where
  default := { p := fun _ => 0, w := fun _ => 0 }

/-- Hyperbolic split pairing on `R^5 ⊕ R^5`. -/
def splitPair (x y : Split55) : ℝ :=
  Finset.univ.sum (fun i : Fin 5 => x.p i * y.w i + x.w i * y.p i)

/-- Flip the first coordinate of a five-vector. -/
def flipFirst (v : Fin 5 → ℝ) : Fin 5 → ℝ :=
  fun i => if i = 0 then -v i else v i

/-- Add a scalar to the second coordinate of a five-vector. -/
def addAtOne (a : ℝ) (v : Fin 5 → ℝ) : Fin 5 → ℝ :=
  fun i => if i = 1 then v i + a else v i

-- LEMMAS

lemma flipFirst_mul_flipFirst (v w : Fin 5 → ℝ) (i : Fin 5) :
    flipFirst v i * flipFirst w i = v i * w i := by
  by_cases h : i = 0
  · simp [flipFirst, h]
  · simp [flipFirst, h]

lemma flipFirst_involutive (v : Fin 5 → ℝ) : flipFirst (flipFirst v) = v := by
  funext i
  by_cases h : i = 0 <;> simp [flipFirst, h]

lemma addAtOne_add (a b : ℝ) (v : Fin 5 → ℝ) : addAtOne a (addAtOne b v) = addAtOne (a + b) v := by
  funext i
  by_cases h : i = 1
  · simp [addAtOne, h]; ring
  · simp [addAtOne, h]

lemma flipFirst_addAtOne_comm (a : ℝ) (v : Fin 5 → ℝ) : flipFirst (addAtOne a v) = addAtOne a (flipFirst v) := by
  funext i
  by_cases h0 : i = 0
  · subst i
    simp [flipFirst, addAtOne]
  · by_cases h1 : i = 1
    · subst i
      simp [flipFirst, addAtOne]
    · simp [flipFirst, addAtOne, h0, h1]

-- END LEMMAS

/-- Pin-style reflection flipping the first split pair. -/
def pinReflection (x : Split55) : Split55 :=
  { p := flipFirst x.p, w := flipFirst x.w }

/-- Translation along an invariant positive coordinate. -/
def translateP (a : ℝ) (x : Split55) : Split55 :=
  { p := addAtOne a x.p, w := x.w }

/-- Glide: first reflect, then translate by a half-step along an invariant coordinate. -/
def glide (x : Split55) : Split55 :=
  translateP (1 / 2) (pinReflection x)

/-- The first-pair sign reflection preserves the split `O(5,5)` pairing. -/
theorem pinReflection_preserves_splitPair (x y : Split55) :
    splitPair (pinReflection x) (pinReflection y) = splitPair x y := by
  unfold splitPair pinReflection
  apply Finset.sum_congr rfl
  intro i _
  dsimp
  rw [flipFirst_mul_flipFirst, flipFirst_mul_flipFirst]

/-- The first-pair sign reflection is an involution. -/
theorem pinReflection_involutive (x : Split55) :
    pinReflection (pinReflection x) = x := by
  apply Split55.ext
  · exact flipFirst_involutive x.p
  · exact flipFirst_involutive x.w

/-- Translations along the invariant coordinate add. -/
theorem translateP_add (a b : ℝ) (x : Split55) :
    translateP a (translateP b x) = translateP (a + b) x := by
  apply Split55.ext
  · exact addAtOne_add a b x.p
  · rfl

/-- The reflection commutes with translations along the chosen invariant coordinate. -/
theorem pinReflection_translateP_comm (a : ℝ) (x : Split55) :
    pinReflection (translateP a x) = translateP a (pinReflection x) := by
  apply Split55.ext
  · exact flipFirst_addAtOne_comm a x.p
  · rfl

/-- The glide squares to a unit translation. -/
theorem glide_square_eq_translation (x : Split55) :
    glide (glide x) = translateP 1 x := by
  unfold glide
  rw [pinReflection_translateP_comm]
  rw [pinReflection_involutive]
  rw [translateP_add]
  norm_num

end InfoGeometry.Clifford.Pin55ReflectionGlide

end noncomputable section

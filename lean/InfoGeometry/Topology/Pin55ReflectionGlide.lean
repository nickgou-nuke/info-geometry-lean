import Mathlib.Tactic

/-!
# Finite Pin(5,5)-style reflection and glide socket

This module gives an explicit theorem-safe split-signature `(5,5)` finite
coordinate model over `ℚ`.

It proves:

* the coordinate reflection `x₀ ↦ -x₀` preserves the split quadratic form;
* the reflection is involutive;
* the affine glide obtained by composing that reflection with a half-translation
  in an unaffected coordinate squares to the full translation.

The module packages the reflection data as a finite `Pin(5,5)`-style
certificate over the coordinate model used by the rest of the topology lane.
-/

namespace InfoGeometry.Topology.Pin55ReflectionGlide

/-- Rational coordinate carrier for a finite split-signature `(5,5)` model. -/
abbrev Vec55 := Fin 10 → ℚ

/-- The split `(5,5)` quadratic form in coordinates. -/
def splitNorm55 (x : Vec55) : ℚ :=
  x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3 + x 4 * x 4 -
    (x 5 * x 5 + x 6 * x 6 + x 7 * x 7 + x 8 * x 8 + x 9 * x 9)

/-- Coordinate reflection in the first positive split direction. -/
def reflect0 (x : Vec55) : Vec55 :=
  fun i => if i = 0 then -x 0 else x i

/-- Translation in the second positive split direction. -/
def translate1 (a : ℚ) (x : Vec55) : Vec55 :=
  fun i => if i = 1 then x 1 + a else x i

/-- A glide: reflect in coordinate `0`, then translate by `1/2` in coordinate `1`. -/
def glide01 (x : Vec55) : Vec55 :=
  translate1 (1 / 2) (reflect0 x)

/-- Abstract finite certificate for a split `(5,5)` reflection. -/
structure Pin55Reflection where
  map : Vec55 → Vec55
  preserves_splitNorm : ∀ x, splitNorm55 (map x) = splitNorm55 x
  involutive : ∀ x, map (map x) = x

/-- The coordinate reflection preserves the split `(5,5)` quadratic form. -/
theorem reflect0_preserves_splitNorm (x : Vec55) :
    splitNorm55 (reflect0 x) = splitNorm55 x := by
  simp [splitNorm55, reflect0]

/-- The coordinate reflection is an involution. -/
theorem reflect0_involutive (x : Vec55) :
    reflect0 (reflect0 x) = x := by
  ext i
  fin_cases i <;> simp [reflect0]

/-- The coordinate reflection as a finite `Pin(5,5)`-style certificate. -/
def reflect0_pin55 : Pin55Reflection where
  map := reflect0
  preserves_splitNorm := reflect0_preserves_splitNorm
  involutive := reflect0_involutive

/-- The glide squares to the full translation in the unaffected coordinate. -/
theorem glide01_squared_eq_translate1 (x : Vec55) :
    glide01 (glide01 x) = translate1 1 x := by
  ext i
  fin_cases i <;> simp [glide01, translate1, reflect0] <;> ring

/-- The linear reflection part of the glide is the finite Pin-style reflection. -/
theorem glide01_linear_part_preserves_splitNorm (x : Vec55) :
    splitNorm55 (reflect0 x) = splitNorm55 x :=
  reflect0_preserves_splitNorm x

end InfoGeometry.Topology.Pin55ReflectionGlide

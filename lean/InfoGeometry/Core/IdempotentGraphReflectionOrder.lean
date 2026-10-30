/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-!
# Graph idempotents and ordered reflection products

For an idempotent `p` in an associative ring, the two Peirce graph points are
idempotents. Their associated involutions have order-sensitive products. The
formulas below retain the order of multiplication and require no division or
commutativity.
-/

namespace InfoGeometry.Core.IdempotentGraphReflectionOrder

variable {B : Type*} [Ring B]

def upperCorner (p a : B) : B := p * a * (1 - p)
def lowerCorner (p c : B) : B := (1 - p) * c * p

def upperGraph (p a : B) : B := p - upperCorner p a
def lowerGraph (p c : B) : B := p + lowerCorner p c

def pointReflection (q : B) : B := q - (1 - q)
def baseReflection (p : B) : B := p - (1 - p)

def chord (p a c : B) : B := upperCorner p a + lowerCorner p c
def midpointDefect (p a c : B) : B := upperCorner p a - lowerCorner p c
def overlap (p a c : B) : B :=
  upperCorner p a * lowerCorner p c + lowerCorner p c * upperCorner p a
def commutatorArea (p a c : B) : B :=
  upperCorner p a * lowerCorner p c - lowerCorner p c * upperCorner p a

lemma p_mul_complement {p : B} (hp : p * p = p) : p * (1 - p) = 0 := by
  calc
    p * (1 - p) = p - p * p := by noncomm_ring
    _ = 0 := by rw [hp]; simp

lemma complement_mul_p {p : B} (hp : p * p = p) : (1 - p) * p = 0 := by
  calc
    (1 - p) * p = p - p * p := by noncomm_ring
    _ = 0 := by rw [hp]; simp

lemma complement_idempotent {p : B} (hp : p * p = p) :
    (1 - p) * (1 - p) = 1 - p := by
  calc
    (1 - p) * (1 - p) = 1 - p - p + p * p := by noncomm_ring
    _ = 1 - p := by rw [hp]; abel

lemma upperCorner_left {p : B} (hp : p * p = p) (a : B) :
    p * upperCorner p a = upperCorner p a := by
  unfold upperCorner
  calc
    p * (p * a * (1 - p)) = (p * p) * a * (1 - p) := by noncomm_ring
    _ = p * a * (1 - p) := by rw [hp]

lemma upperCorner_right {p : B} (hp : p * p = p) (a : B) :
    upperCorner p a * p = 0 := by
  unfold upperCorner
  calc
    p * a * (1 - p) * p = p * a * ((1 - p) * p) := by noncomm_ring
    _ = 0 := by rw [complement_mul_p hp]; simp

lemma upperCorner_sq {p : B} (hp : p * p = p) (a : B) :
    upperCorner p a * upperCorner p a = 0 := by
  unfold upperCorner
  calc
    (p * a * (1 - p)) * (p * a * (1 - p)) =
        p * a * ((1 - p) * p) * a * (1 - p) := by noncomm_ring
    _ = 0 := by rw [complement_mul_p hp]; simp

lemma lowerCorner_left {p : B} (hp : p * p = p) (c : B) :
    p * lowerCorner p c = 0 := by
  unfold lowerCorner
  calc
    p * ((1 - p) * c * p) = (p * (1 - p)) * c * p := by noncomm_ring
    _ = 0 := by rw [p_mul_complement hp]; simp

lemma lowerCorner_right {p : B} (hp : p * p = p) (c : B) :
    lowerCorner p c * p = lowerCorner p c := by
  unfold lowerCorner
  calc
    (1 - p) * c * p * p = (1 - p) * c * (p * p) := by noncomm_ring
    _ = (1 - p) * c * p := by rw [hp]

lemma lowerCorner_sq {p : B} (hp : p * p = p) (c : B) :
    lowerCorner p c * lowerCorner p c = 0 := by
  unfold lowerCorner
  calc
    ((1 - p) * c * p) * ((1 - p) * c * p) =
        (1 - p) * c * (p * (1 - p)) * c * p := by noncomm_ring
    _ = 0 := by rw [p_mul_complement hp]; simp

lemma upperCorner_complement_left {p : B} (hp : p * p = p) (a : B) :
    (1 - p) * upperCorner p a = 0 := by
  unfold upperCorner
  calc
    (1 - p) * (p * a * (1 - p)) = ((1 - p) * p) * a * (1 - p) := by noncomm_ring
    _ = 0 := by rw [complement_mul_p hp]; simp

lemma upperCorner_complement_right {p : B} (hp : p * p = p) (a : B) :
    upperCorner p a * (1 - p) = upperCorner p a := by
  unfold upperCorner
  calc
    p * a * (1 - p) * (1 - p) = p * a * ((1 - p) * (1 - p)) := by noncomm_ring
    _ = p * a * (1 - p) := by rw [complement_idempotent hp]

lemma lowerCorner_complement_left {p : B} (hp : p * p = p) (c : B) :
    (1 - p) * lowerCorner p c = lowerCorner p c := by
  unfold lowerCorner
  calc
    (1 - p) * ((1 - p) * c * p) = ((1 - p) * (1 - p)) * c * p := by noncomm_ring
    _ = (1 - p) * c * p := by rw [complement_idempotent hp]

lemma lowerCorner_complement_right {p : B} (hp : p * p = p) (c : B) :
    lowerCorner p c * (1 - p) = 0 := by
  unfold lowerCorner
  calc
    (1 - p) * c * p * (1 - p) = (1 - p) * c * (p * (1 - p)) := by noncomm_ring
    _ = 0 := by rw [p_mul_complement hp]; simp

lemma baseReflection_sq {p : B} (hp : p * p = p) :
    baseReflection p * baseReflection p = 1 := by
  unfold baseReflection
  calc
    (p - (1 - p)) * (p - (1 - p)) =
        p * p - p * (1 - p) - (1 - p) * p + (1 - p) * (1 - p) := by noncomm_ring
    _ = 1 := by rw [hp, p_mul_complement hp, complement_mul_p hp, complement_idempotent hp]; abel

lemma baseReflection_mul_upper {p : B} (hp : p * p = p) (a : B) :
    baseReflection p * upperCorner p a = upperCorner p a := by
  unfold baseReflection
  calc
    (p - (1 - p)) * upperCorner p a =
        p * upperCorner p a - (1 - p) * upperCorner p a := by noncomm_ring
    _ = upperCorner p a := by rw [upperCorner_left hp, upperCorner_complement_left hp]; simp

lemma upper_mul_baseReflection {p : B} (hp : p * p = p) (a : B) :
    upperCorner p a * baseReflection p = -upperCorner p a := by
  unfold baseReflection
  calc
    upperCorner p a * (p - (1 - p)) =
        upperCorner p a * p - upperCorner p a * (1 - p) := by noncomm_ring
    _ = -upperCorner p a := by rw [upperCorner_right hp, upperCorner_complement_right hp]; simp

lemma baseReflection_mul_lower {p : B} (hp : p * p = p) (c : B) :
    baseReflection p * lowerCorner p c = -lowerCorner p c := by
  unfold baseReflection
  calc
    (p - (1 - p)) * lowerCorner p c =
        p * lowerCorner p c - (1 - p) * lowerCorner p c := by noncomm_ring
    _ = -lowerCorner p c := by rw [lowerCorner_left hp, lowerCorner_complement_left hp]; simp

lemma lower_mul_baseReflection {p : B} (hp : p * p = p) (c : B) :
    lowerCorner p c * baseReflection p = lowerCorner p c := by
  unfold baseReflection
  calc
    lowerCorner p c * (p - (1 - p)) =
        lowerCorner p c * p - lowerCorner p c * (1 - p) := by noncomm_ring
    _ = lowerCorner p c := by rw [lowerCorner_right hp, lowerCorner_complement_right hp]; simp

theorem upperGraph_idempotent {p : B} (hp : p * p = p) (a : B) :
    upperGraph p a * upperGraph p a = upperGraph p a := by
  unfold upperGraph
  calc
    (p - upperCorner p a) * (p - upperCorner p a) =
        p * p - p * upperCorner p a - upperCorner p a * p +
          upperCorner p a * upperCorner p a := by noncomm_ring
    _ = p - upperCorner p a := by
      rw [hp, upperCorner_left hp, upperCorner_right hp, upperCorner_sq hp]
      simp

theorem lowerGraph_idempotent {p : B} (hp : p * p = p) (c : B) :
    lowerGraph p c * lowerGraph p c = lowerGraph p c := by
  unfold lowerGraph
  calc
    (p + lowerCorner p c) * (p + lowerCorner p c) =
        p * p + p * lowerCorner p c + lowerCorner p c * p +
          lowerCorner p c * lowerCorner p c := by noncomm_ring
    _ = p + lowerCorner p c := by
      rw [hp, lowerCorner_left hp, lowerCorner_right hp, lowerCorner_sq hp]
      simp

lemma pointReflection_upperGraph {p : B} (a : B) :
    pointReflection (upperGraph p a) =
      baseReflection p - upperCorner p a - upperCorner p a := by
  unfold pointReflection upperGraph baseReflection
  noncomm_ring

lemma pointReflection_lowerGraph {p : B} (c : B) :
    pointReflection (lowerGraph p c) =
      baseReflection p + lowerCorner p c + lowerCorner p c := by
  unfold pointReflection lowerGraph baseReflection
  noncomm_ring

/-- The forward ordered product; reversing the factors changes both linear and
quadratic terms. -/
theorem pointReflection_upper_mul_lower {p : B} (hp : p * p = p) (a c : B) :
    pointReflection (upperGraph p a) * pointReflection (lowerGraph p c) =
      1 + midpointDefect p a c + midpointDefect p a c -
        commutatorArea p a c - commutatorArea p a c - overlap p a c - overlap p a c := by
  rw [pointReflection_upperGraph, pointReflection_lowerGraph]
  unfold midpointDefect commutatorArea overlap
  calc
    (baseReflection p - upperCorner p a - upperCorner p a) *
        (baseReflection p + lowerCorner p c + lowerCorner p c) =
        baseReflection p * baseReflection p +
          baseReflection p * lowerCorner p c + baseReflection p * lowerCorner p c -
          upperCorner p a * baseReflection p - upperCorner p a * baseReflection p -
          upperCorner p a * lowerCorner p c - upperCorner p a * lowerCorner p c -
          upperCorner p a * lowerCorner p c - upperCorner p a * lowerCorner p c := by noncomm_ring
    _ = 1 + upperCorner p a + upperCorner p a - lowerCorner p c - lowerCorner p c -
          upperCorner p a * lowerCorner p c - upperCorner p a * lowerCorner p c -
          upperCorner p a * lowerCorner p c - upperCorner p a * lowerCorner p c := by
      rw [baseReflection_sq hp, baseReflection_mul_lower hp, upper_mul_baseReflection hp]
      noncomm_ring
    _ = 1 + (upperCorner p a - lowerCorner p c) + (upperCorner p a - lowerCorner p c) -
          (upperCorner p a * lowerCorner p c - lowerCorner p c * upperCorner p a) -
          (upperCorner p a * lowerCorner p c - lowerCorner p c * upperCorner p a) -
          (upperCorner p a * lowerCorner p c + lowerCorner p c * upperCorner p a) -
          (upperCorner p a * lowerCorner p c + lowerCorner p c * upperCorner p a) := by
      noncomm_ring

/-- The reverse ordered product, which is the expression incorrectly assigned
to the forward product in the supplied A₂₄ claim. -/
theorem pointReflection_lower_mul_upper {p : B} (hp : p * p = p) (a c : B) :
    pointReflection (lowerGraph p c) * pointReflection (upperGraph p a) =
      1 - midpointDefect p a c - midpointDefect p a c +
        commutatorArea p a c + commutatorArea p a c - overlap p a c - overlap p a c := by
  rw [pointReflection_lowerGraph, pointReflection_upperGraph]
  unfold midpointDefect commutatorArea overlap
  calc
    (baseReflection p + lowerCorner p c + lowerCorner p c) *
        (baseReflection p - upperCorner p a - upperCorner p a) =
        baseReflection p * baseReflection p -
          baseReflection p * upperCorner p a - baseReflection p * upperCorner p a +
          lowerCorner p c * baseReflection p + lowerCorner p c * baseReflection p -
          lowerCorner p c * upperCorner p a - lowerCorner p c * upperCorner p a -
          lowerCorner p c * upperCorner p a - lowerCorner p c * upperCorner p a := by noncomm_ring
    _ = 1 - upperCorner p a - upperCorner p a + lowerCorner p c + lowerCorner p c -
          lowerCorner p c * upperCorner p a - lowerCorner p c * upperCorner p a -
          lowerCorner p c * upperCorner p a - lowerCorner p c * upperCorner p a := by
      rw [baseReflection_sq hp, baseReflection_mul_upper hp, lower_mul_baseReflection hp]
    _ = 1 - (upperCorner p a - lowerCorner p c) - (upperCorner p a - lowerCorner p c) +
          (upperCorner p a * lowerCorner p c - lowerCorner p c * upperCorner p a) +
          (upperCorner p a * lowerCorner p c - lowerCorner p c * upperCorner p a) -
          (upperCorner p a * lowerCorner p c + lowerCorner p c * upperCorner p a) -
          (upperCorner p a * lowerCorner p c + lowerCorner p c * upperCorner p a) := by
      noncomm_ring

theorem pointReflection_anticommutator {p : B} (hp : p * p = p) (a c : B) :
    pointReflection (upperGraph p a) * pointReflection (lowerGraph p c) +
      pointReflection (lowerGraph p c) * pointReflection (upperGraph p a) =
      1 + 1 - overlap p a c - overlap p a c - overlap p a c - overlap p a c := by
  rw [pointReflection_upper_mul_lower hp, pointReflection_lower_mul_upper hp]
  unfold midpointDefect commutatorArea overlap
  noncomm_ring

theorem pointReflection_commutator {p : B} (hp : p * p = p) (a c : B) :
    pointReflection (upperGraph p a) * pointReflection (lowerGraph p c) -
      pointReflection (lowerGraph p c) * pointReflection (upperGraph p a) =
      midpointDefect p a c + midpointDefect p a c + midpointDefect p a c + midpointDefect p a c -
        commutatorArea p a c - commutatorArea p a c - commutatorArea p a c - commutatorArea p a c := by
  rw [pointReflection_upper_mul_lower hp, pointReflection_lower_mul_upper hp]
  unfold midpointDefect commutatorArea overlap
  noncomm_ring

/-- Compact form of the ordered commutator: in the upper-then-lower order the
sign is midpoint defect minus corner commutator area. -/
theorem pointReflection_commutator_compact {p : B} (hp : p * p = p) (a c : B) :
    pointReflection (upperGraph p a) * pointReflection (lowerGraph p c) -
      pointReflection (lowerGraph p c) * pointReflection (upperGraph p a) =
      4 * (midpointDefect p a c - commutatorArea p a c) := by
  rw [pointReflection_commutator hp a c]
  unfold midpointDefect commutatorArea
  noncomm_ring

/-! A concrete matrix witness separates the two orders. The inputs are
off-diagonal matrix units, so the example is genuinely noncommutative. -/

abbrev WitnessMatrix := Matrix (Fin 2) (Fin 2) ℤ

def witnessP : WitnessMatrix := Matrix.single 0 0 1
def witnessA : WitnessMatrix := Matrix.single 0 1 1
def witnessC : WitnessMatrix := Matrix.single 1 0 1

theorem matrix_reflection_products_are_order_distinct :
    pointReflection (upperGraph witnessP witnessA) *
        pointReflection (lowerGraph witnessP witnessC) ≠
      pointReflection (lowerGraph witnessP witnessC) *
        pointReflection (upperGraph witnessP witnessA) := by
  decide

/-- The proposed A₂₄ forward-product formula has the reverse ordering's signs.
The noncommuting matrix-unit witness refutes it; the valid forward formula is
`pointReflection_upper_mul_lower`, while `pointReflection_lower_mul_upper`
has the displayed right-hand side. -/
theorem matrix_counterexample_reversed_forward_reflection_formula :
    pointReflection (upperGraph witnessP witnessA) *
        pointReflection (lowerGraph witnessP witnessC) ≠
      1 - (2 : ℕ) • midpointDefect witnessP witnessA witnessC +
        (2 : ℕ) • commutatorArea witnessP witnessA witnessC -
        (2 : ℕ) • overlap witnessP witnessA witnessC := by
  decide

/-- The same noncommuting matrix units refute the opposite sign proposed for
the commutator of the upper-then-lower reflection product. -/
theorem matrix_counterexample_reversed_reflection_commutator_sign :
    pointReflection (upperGraph witnessP witnessA) *
        pointReflection (lowerGraph witnessP witnessC) -
      pointReflection (lowerGraph witnessP witnessC) *
        pointReflection (upperGraph witnessP witnessA) ≠
      4 * (commutatorArea witnessP witnessA witnessC -
        midpointDefect witnessP witnessA witnessC) := by
  decide

end InfoGeometry.Core.IdempotentGraphReflectionOrder

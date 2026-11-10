/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Clifford.QuadraticPolarAnticommutator

Quadratic/polar to Clifford anticommutator bridge.

If a generator map satisfies the Clifford square relation

  `ι v * ι v = algebraMap R A (Q v)`,

then its anticommutator is the polar expression

  `Q (x + y) - Q x - Q y`.
-/

namespace InfoGeometry.Clifford

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem quadraticPolar_exists_noncomm_pair :
    ∃ a b : _root_.InfoGeometry.Algebra.FiniteSpin.Mat2C, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/--
Polar expression attached to a quadratic function.
-/
def polarFromQuadratic
    {R V : Type*} [Sub R] [Add V]
    (Q : V → R) (x y : V) : R :=
  Q (x + y) - Q x - Q y

/-- Operator-valued Clifford anticommutator from the square relation over any non-commutative ring `[Ring B]`. -/
theorem ring_anticommutator_from_square_relation
    {V B : Type*} [Add V] [Ring B]
    (Q : V → B) (ι : V → B)
    (hadd : ∀ x y : V, ι (x + y) = ι x + ι y)
    (hsq : ∀ v : V, ι v * ι v = Q v)
    (x y : V) :
    ι x * ι y + ι y * ι x = polarFromQuadratic Q x y := by
  unfold polarFromQuadratic
  have hxy := hsq (x + y)
  rw [hadd x y] at hxy
  have hexpand :
      (ι x + ι y) * (ι x + ι y) =
        ι x * ι x + (ι x * ι y + ι y * ι x) + ι y * ι y := by
    noncomm_ring
  calc
    ι x * ι y + ι y * ι x =
      (ι x + ι y) * (ι x + ι y) - ι x * ι x - ι y * ι y := by
        rw [hexpand]; abel
    _ = Q (x + y) - Q x - Q y := by
        rw [hxy, hsq x, hsq y]

/--
Clifford anticommutator from the square relation.
-/
theorem clifford_anticommutator_from_square_relation
    {R V A : Type*}
    [CommRing R]
    [AddCommGroup V]
    [Ring A] [Algebra R A]
    (Q : V → R)
    (ι : V → A)
    (hadd : ∀ x y : V, ι (x + y) = ι x + ι y)
    (hsq : ∀ v : V, ι v * ι v = algebraMap R A (Q v))
    (x y : V) :
    ι x * ι y + ι y * ι x =
      algebraMap R A (polarFromQuadratic Q x y) := by
  unfold polarFromQuadratic

  have hxy := hsq (x + y)
  rw [hadd x y] at hxy

  have hexpand :
      (ι x + ι y) * (ι x + ι y)
        =
      ι x * ι x + (ι x * ι y + ι y * ι x) + ι y * ι y := by
    noncomm_ring

  have hsum :
      ι x * ι x + (ι x * ι y + ι y * ι x) + ι y * ι y
        =
      algebraMap R A (Q (x + y)) := by
    rw [← hxy]
    exact hexpand.symm

  calc
    ι x * ι y + ι y * ι x
        =
      (ι x * ι x + (ι x * ι y + ι y * ι x) + ι y * ι y)
        - ι x * ι x - ι y * ι y := by
          abel
    _ =
      algebraMap R A (Q (x + y))
        - algebraMap R A (Q x)
        - algebraMap R A (Q y) := by
          rw [hsum, hsq x, hsq y]
    _ =
      algebraMap R A (Q (x + y) - Q x - Q y) := by
          rw [map_sub, map_sub]

end InfoGeometry.Clifford


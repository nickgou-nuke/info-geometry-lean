/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-!
# Hestenes–Ziegler §4.2: the Pappus bracket identity in `P²`

Source: D. Hestenes and R. Ziegler, *Projective Geometry with Clifford Algebra*,
Acta Appl. Math. 23 (1991) 25–63, §4.2, Eq. (4.15).

In the paper the Pappus theorem is the scalar-part identity in `G₃`

  `⟨(a∧a')(b∧b')(c∧c')⟩ + ⟨(a∧b')(b∧c')(c∧a')⟩ + ⟨(a∧c')(b∧a')(c∧b')⟩ = 0`.

Expanding each scalar triple product with the paper's Eq. (2.32),
`⟨ABC⟩ = (A∧c)·(B∧c') − (A∧c')·(B∧c)` for `C = c∧c'`, and writing the
3-bracket as the ordered determinant `[xyz] = b.det ![x,y,z]` (equivalently
`volCoord b (ι x ∧ ι y ∧ ι z)`), the identity becomes the pure determinant
identity proved below.  The common pseudoscalar-square factor `I²` from the
inner product of two 3-blades is a nonzero scalar and cancels, so the bracket
identity is exactly the projective content.

This file states the identity over an arbitrary field and an arbitrary
3-dimensional basis; it is a polynomial identity in the vector coordinates and
is discharged by `ring`.  No metric, duality witness, or Clifford-grade
projection is assumed.  The geometric Pappus concurrence statement is the
projective interpretation of this algebraic identity and is not separately
asserted here.
-/

noncomputable section

namespace InfoGeometry.Projective.HestenesZieglerPappus

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The ordered 3-bracket `[xyz]` in the basis `b`, i.e. the determinant of the
three coordinate columns.  This is the paper's bracket `[x y z]`. -/
def bracket3 (b : Module.Basis (Fin 3) K V) (x y z : V) : K :=
  b.det ![x, y, z]

/-- **Hestenes–Ziegler Eq. (4.15), bracket form.**  The three Pappus pairings of
six points `a, a', b, b', c, c'` in `P²` satisfy the alternating determinant
identity obtained by expanding each `G₃` scalar triple product via Eq. (2.32).
This is the algebraic form of Pappus's theorem. -/
theorem pappus_bracket_identity (b : Module.Basis (Fin 3) K V)
    (a a' b₁ b₁' c c' : V) :
    (bracket3 b a a' c * bracket3 b b₁ b₁' c' - bracket3 b a a' c' * bracket3 b b₁ b₁' c)
    + (bracket3 b a b₁' c * bracket3 b b₁ c' a' - bracket3 b a b₁' a' * bracket3 b b₁ c' c)
    + (bracket3 b a c' c * bracket3 b b₁ a' b₁' - bracket3 b a c' b₁' * bracket3 b b₁ a' c)
    = 0 := by
  simp [bracket3, Module.Basis.det_apply, Module.Basis.toMatrix_apply,
    Matrix.det_fin_three]
  ring

end InfoGeometry.Projective.HestenesZieglerPappus

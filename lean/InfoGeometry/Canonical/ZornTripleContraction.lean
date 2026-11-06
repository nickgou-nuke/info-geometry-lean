/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornAssociatorKreinBridge
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # A bracketed triple contraction in the full Zorn algebra

The full split-octonion product has a nonzero same-upper-sector cross product.
It is not the associative Peirce ring product. Both terms below retain the
parenthesized product of the first two upper vectors; no associativity is used.
-/

namespace InfoGeometry.Canonical.ZornAssociatorKreinBridge

open InfoGeometry.Algebra.SplitOctonionZorn

/-- The scalar triple product agrees with the native determinant whose rows
are the three ordered vectors. -/
theorem tripleDet_eq_matrix_det (u v w : Vec3) :
    tripleDet u v w =
      Matrix.det !![u.x, u.y, u.z; v.x, v.y, v.z; w.x, w.y, w.z] := by
  simp [tripleDet, Vector3.dot, Vector3.cross, Matrix.det_fin_three]
  ring

/-- The anticommutator of the ordered upper-pair product with the third
upper vector is the native determinant times the algebraic unit. -/
theorem upper_triple_anticommutator (u v w : Vec3) :
    (upper u * upper v) * upper w + upper w * (upper u * upper v) =
      Matrix.det !![u.x, u.y, u.z; v.x, v.y, v.z; w.x, w.y, w.z] • (1 : Zorn) := by
  rw [← tripleDet_eq_matrix_det]
  simp only [upper_mul_upper, lower_mul_upper, upper_mul_lower]
  rw [tripleDet_cyclic w u v, ← smul_add,
    add_comm SplitOctonion.idempotentE2 SplitOctonion.idempotentE1,
    peirce_idempotents_sum]

end InfoGeometry.Canonical.ZornAssociatorKreinBridge

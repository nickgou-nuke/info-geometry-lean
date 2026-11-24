/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Bilinear cotangent pairing and signed graph restrictions

On the actual vector space `V × Module.Dual ℝ V`, the form is
`Ω((x,ν),(y,μ)) = μ(x) - ν(y) + B(x,y)`. If `B` is alternating,
its pullback along `x ↦ (x,t • B x)` is `(1 - 2*t) • B`.
Thus the positive graph gives `-B` and the negative graph gives `3 • B`.
This is linear algebra; identifying a graph with orbit tangents or proving
closedness of a manifold differential form requires additional constructions.
-/

noncomputable section

namespace InfoGeometry.Algebraic.CotangentBilinearGraph

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The bilinear form on vectors and their native linear duals. -/
def cotangentForm (B : LinearMap.BilinForm ℝ V) :
    LinearMap.BilinForm ℝ (V × Module.Dual ℝ V) :=
  let vector := LinearMap.fst ℝ V (Module.Dual ℝ V)
  let covector := LinearMap.snd ℝ V (Module.Dual ℝ V)
  let evaluation := (LinearMap.id : Module.Dual ℝ V →ₗ[ℝ] Module.Dual ℝ V)
  evaluation.flip.compl₁₂ vector covector -
    evaluation.compl₁₂ covector vector + B.compl₁₂ vector vector

@[simp] theorem cotangentForm_apply (B : LinearMap.BilinForm ℝ V)
    (v w : V × Module.Dual ℝ V) :
    cotangentForm B v w = w.2 v.1 - v.2 w.1 + B v.1 w.1 := rfl

/-- Native linear inclusion of the graph of the scaled bilinear dual map. -/
def signedGraph (B : LinearMap.BilinForm ℝ V) (t : ℝ) :
    V →ₗ[ℝ] (V × Module.Dual ℝ V) :=
  (LinearMap.id : V →ₗ[ℝ] V).prod (t • B)

@[simp] theorem signedGraph_apply (B : LinearMap.BilinForm ℝ V)
    (t : ℝ) (x : V) : signedGraph B t x = (x, t • B x) := rfl

theorem cotangentForm_isAlt (B : LinearMap.BilinForm ℝ V) (hB : B.IsAlt) :
    (cotangentForm B).IsAlt := by
  intro v
  simp only [cotangentForm_apply, sub_self, zero_add]
  exact hB v.1

private theorem signed_graph_scalar (t b : ℝ) :
    t * (-b) - t * b + b = (1 - 2 * t) * b := by
  ring

/-- The scalar coefficient records the sign convention without identifying
either graph with a manifold tangent space. -/
theorem cotangentForm_signedGraph (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsAlt) (t : ℝ) (x y : V) :
    cotangentForm B (signedGraph B t x) (signedGraph B t y) =
      (1 - 2 * t) * B x y := by
  simp only [cotangentForm_apply, signedGraph_apply, LinearMap.smul_apply,
    smul_eq_mul]
  rw [← hB.neg_eq x y]
  exact signed_graph_scalar t (B x y)

/-- Equality of native bilinear forms after pulling back along the graph. -/
theorem cotangentForm_pullback_signedGraph (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsAlt) (t : ℝ) :
    (cotangentForm B).compl₁₂ (signedGraph B t) (signedGraph B t) =
      (1 - 2 * t) • B := by
  ext x y
  exact cotangentForm_signedGraph B hB t x y

theorem cotangentForm_positiveGraph (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsAlt) (x y : V) :
    cotangentForm B (signedGraph B 1 x) (signedGraph B 1 y) = -B x y := by
  rw [cotangentForm_signedGraph B hB]
  norm_num

theorem cotangentForm_negativeGraph (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsAlt) (x y : V) :
    cotangentForm B (signedGraph B (-1) x) (signedGraph B (-1) y) =
      3 * B x y := by
  rw [cotangentForm_signedGraph B hB]
  norm_num

private theorem three_mul_ne_neg {b : ℝ} (hb : b ≠ 0) : 3 * b ≠ -b := by
  intro h
  apply hb
  linarith

/-- Every nonzero value detects the rejected negative-graph sign. -/
theorem negativeGraph_ne_negative_pairing (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsAlt) (x y : V) (hxy : B x y ≠ 0) :
    cotangentForm B (signedGraph B (-1) x) (signedGraph B (-1) y) ≠
      -B x y := by
  rw [cotangentForm_negativeGraph B hB]
  exact three_mul_ne_neg hxy

/-- The ordinary alternating area form supplies a nonzero real example. -/
def planeArea : LinearMap.BilinForm ℝ (ℝ × ℝ) :=
  let first := LinearMap.fst ℝ ℝ ℝ
  let second := LinearMap.snd ℝ ℝ ℝ
  (LinearMap.mul ℝ ℝ).compl₁₂ first second -
    (LinearMap.mul ℝ ℝ).compl₁₂ second first

theorem planeArea_isAlt : planeArea.IsAlt := by
  intro x
  change x.1 * x.2 - x.2 * x.1 = 0
  rw [mul_comm x.2 x.1, sub_self]

/-- With the abelian two-dimensional Lie bracket and zero base covector,
the twisting area form gives `3`, whereas the rejected formula gives `-1`. -/
theorem negativeGraph_plane_counterexample :
    cotangentForm planeArea (signedGraph planeArea (-1) (1, 0))
      (signedGraph planeArea (-1) (0, 1)) = 3 ∧
    -planeArea (1, 0) (0, 1) = -1 := by
  rw [cotangentForm_negativeGraph planeArea planeArea_isAlt]
  norm_num [planeArea]

end InfoGeometry.Algebraic.CotangentBilinearGraph

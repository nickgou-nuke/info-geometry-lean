/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Basic.Real.Basic

/-!
# Compatible real endomorphisms on a native directed limit

The native module lift constructs each endomorphism on `_root_.DirectLimit`.
Involution, reflection, and commutation laws then follow by checking one
stage representative. No injective transition maps or topological structure
are needed. This file does not introduce another colimit carrier or another
universal-property record.
-/

noncomputable section

namespace InfoGeometry.LinearAlgebra.DirectLimitEndomorphism

variable {I : Type*} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {V : I → Type*}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
variable (f : ∀ i j, i ≤ j → V i →ₗ[ℝ] V j)
variable [DirectedSystem V (fun i j h x => f i j h x)]

/-- The compatible family of endomorphisms acts on the existing root direct
limit through Mathlib's module universal map. -/
def descendEnd (T : ∀ i, V i →ₗ[ℝ] V i)
    (hT : ∀ i j (h : i ≤ j) (x : V i),
      T j (f i j h x) = f i j h (T i x)) :
    _root_.DirectLimit V f →ₗ[ℝ] _root_.DirectLimit V f :=
  DirectLimit.Module.lift ℝ I V f
    (fun i => (DirectLimit.Module.of ℝ I V f i).comp (T i))
    (by
      intro i j h x
      change DirectLimit.Module.of ℝ I V f j (T j (f i j h x)) =
        DirectLimit.Module.of ℝ I V f i (T i x)
      rw [hT, DirectLimit.Module.of_f])

/-- Evaluation on a stage vector is the native lift computation rule. -/
@[simp]
theorem descendEnd_of (T : ∀ i, V i →ₗ[ℝ] V i)
    (hT : ∀ i j (h : i ≤ j) (x : V i),
      T j (f i j h x) = f i j h (T i x))
    (i : I) (x : V i) :
    descendEnd f T hT (DirectLimit.Module.of ℝ I V f i x) =
      DirectLimit.Module.of ℝ I V f i (T i x) := rfl

/-- Stagewise involutions remain involutive on the direct limit. -/
theorem descendEnd_involutive (T : ∀ i, V i →ₗ[ℝ] V i)
    (hT : ∀ i j (h : i ≤ j) (x : V i),
      T j (f i j h x) = f i j h (T i x))
    (hInv : ∀ i, Function.Involutive (T i)) :
    Function.Involutive (descendEnd f T hT) := by
  intro z
  refine DirectLimit.induction f (fun i x => ?_) z
  change descendEnd f T hT
      (descendEnd f T hT (DirectLimit.Module.of ℝ I V f i x)) =
    DirectLimit.Module.of ℝ I V f i x
  simp only [descendEnd_of]
  exact congrArg (DirectLimit.Module.of ℝ I V f i) (hInv i x)

/-- A compatible square-zero endomorphism remains square-zero. This is a
single endomorphism statement, without asserting a graded chain complex. -/
theorem descendEnd_square_zero (T : ∀ i, V i →ₗ[ℝ] V i)
    (hT : ∀ i j (h : i ≤ j) (x : V i),
      T j (f i j h x) = f i j h (T i x))
    (hSq : ∀ i x, T i (T i x) = 0) :
    (descendEnd f T hT).comp (descendEnd f T hT) = 0 := by
  apply LinearMap.ext
  intro z
  refine DirectLimit.induction f (fun i x => ?_) z
  change descendEnd f T hT
      (descendEnd f T hT (DirectLimit.Module.of ℝ I V f i x)) = 0
  simp only [descendEnd_of, hSq, map_zero]

/-- A stage eigen-equation descends even when its image might be zero.
Preserving a nonzero eigenvector requires a separate nonzero-image premise. -/
theorem descendEnd_eigen_equation_of_stage (T : ∀ i, V i →ₗ[ℝ] V i)
    (hT : ∀ i j (h : i ≤ j) (x : V i),
      T j (f i j h x) = f i j h (T i x))
    (i : I) (x : V i) (w : ℝ) (hEigen : T i x = w • x) :
    descendEnd f T hT (DirectLimit.Module.of ℝ I V f i x) =
      w • DirectLimit.Module.of ℝ I V f i x := by
  rw [descendEnd_of, hEigen, map_smul]

/-- Compatible stagewise reflections transport the exact operator identity
`J ∘ D ∘ J = -D` to the direct limit. -/
theorem descendEnd_reflection
    (J D : ∀ i, V i →ₗ[ℝ] V i)
    (hJ : ∀ i j (h : i ≤ j) (x : V i),
      J j (f i j h x) = f i j h (J i x))
    (hD : ∀ i j (h : i ≤ j) (x : V i),
      D j (f i j h x) = f i j h (D i x))
    (hReflection : ∀ i x, J i (D i (J i x)) = -D i x) :
    (descendEnd f J hJ).comp
        ((descendEnd f D hD).comp (descendEnd f J hJ)) =
      -(descendEnd f D hD) := by
  apply LinearMap.ext
  intro z
  refine DirectLimit.induction f (fun i x => ?_) z
  change descendEnd f J hJ
      (descendEnd f D hD
        (descendEnd f J hJ (DirectLimit.Module.of ℝ I V f i x))) =
    -descendEnd f D hD (DirectLimit.Module.of ℝ I V f i x)
  simp only [descendEnd_of, hReflection, map_neg]

/-- Compatible commuting endomorphisms commute on the direct limit. -/
theorem descendEnd_commute
    (S T : ∀ i, V i →ₗ[ℝ] V i)
    (hS : ∀ i j (h : i ≤ j) (x : V i),
      S j (f i j h x) = f i j h (S i x))
    (hT : ∀ i j (h : i ≤ j) (x : V i),
      T j (f i j h x) = f i j h (T i x))
    (hComm : ∀ i, Function.Commute (S i) (T i)) :
    Function.Commute (descendEnd f S hS) (descendEnd f T hT) := by
  intro z
  refine DirectLimit.induction f (fun i x => ?_) z
  change descendEnd f S hS
      (descendEnd f T hT (DirectLimit.Module.of ℝ I V f i x)) =
    descendEnd f T hT
      (descendEnd f S hS (DirectLimit.Module.of ℝ I V f i x))
  simp only [descendEnd_of]
  exact congrArg (DirectLimit.Module.of ℝ I V f i) (hComm i x)

end InfoGeometry.LinearAlgebra.DirectLimitEndomorphism

end

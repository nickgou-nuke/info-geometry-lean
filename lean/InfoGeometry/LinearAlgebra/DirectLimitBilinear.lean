/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Real bilinear forms on a native directed limit

Exact preservation of the stage forms lets Mathlib's `DirectLimit.lift₂`
descend their two arguments. The construction below only bundles that native
function as a bilinear form. The carrier remains `_root_.DirectLimit V f`.

No injectivity, norm, positive definiteness, or finite-dimensionality is
assumed. Nonnegativity is equivalent to stagewise nonnegativity, and a negative
stage vector has a nonzero negative image even if other vectors are killed by
the canonical stage map. No completion or convergence claim is made.
-/

noncomputable section

namespace InfoGeometry.LinearAlgebra.DirectLimitBilinear

variable {I : Type*} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {V : I → Type*}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
variable (f : ∀ i j, i ≤ j → V i →ₗ[ℝ] V j)
variable [DirectedSystem V (fun i j h x => f i j h x)]
variable (B : ∀ i, LinearMap.BilinForm ℝ (V i))
variable (hB : ∀ i j (h : i ≤ j) (x y : V i),
  B j (f i j h x) (f i j h y) = B i x y)

/-- The compatible stage forms descend to a real bilinear form on Mathlib's
existing directed-limit carrier. Representative independence is supplied by
`DirectLimit.lift₂`; bilinearity is checked at one common stage. -/
def form : LinearMap.BilinForm ℝ (_root_.DirectLimit V f) :=
  LinearMap.mk₂ ℝ
    (DirectLimit.lift₂ f f (fun i x y => B i x y)
      (fun i j h x y => (hB i j h x y).symm))
    (by
      intro x₁ x₂ y
      refine DirectLimit.induction₃ f (fun i a b c => ?_) x₁ x₂ y
      rw [DirectLimit.add_def]
      simp only [DirectLimit.lift₂_def]
      exact LinearMap.map_add₂ (B i) a b c)
    (by
      intro r x y
      refine DirectLimit.induction₂ f (fun i a b => ?_) x y
      rw [DirectLimit.smul_def]
      simp only [DirectLimit.lift₂_def]
      exact LinearMap.map_smul₂ (B i) r a b)
    (by
      intro x y₁ y₂
      refine DirectLimit.induction₃ f (fun i a b c => ?_) x y₁ y₂
      rw [DirectLimit.add_def]
      simp only [DirectLimit.lift₂_def]
      exact (B i a).map_add b c)
    (by
      intro r x y
      refine DirectLimit.induction₂ f (fun i a b => ?_) x y
      rw [DirectLimit.smul_def]
      simp only [DirectLimit.lift₂_def]
      exact (B i a).map_smul r b)

/-- Same-stage evaluation recovers the original form exactly. -/
@[simp]
theorem form_of (i : I) (x y : V i) :
    form f B hB (DirectLimit.Module.of ℝ I V f i x)
      (DirectLimit.Module.of ℝ I V f i y) = B i x y :=
  DirectLimit.lift₂_def f f (fun i x y => B i x y)
    (fun i j h x y => (hB i j h x y).symm) i x y

/-- Evaluation on any two representatives may use any common upper stage. -/
theorem form_of_of (i j k : I) (hik : i ≤ k) (hjk : j ≤ k)
    (x : V i) (y : V j) :
    form f B hB (DirectLimit.Module.of ℝ I V f i x)
      (DirectLimit.Module.of ℝ I V f j y) =
      B k (f i k hik x) (f j k hjk y) :=
  DirectLimit.lift₂_def₂ f f (fun i x y => B i x y)
    (fun i j h x y => (hB i j h x y).symm)
    ⟨i, x⟩ ⟨j, y⟩ k hik hjk

/-- A bilinear form with the same evaluations on every stage is the descended
form. The common-stage induction can identify an existing concrete pairing
with this construction. -/
theorem form_unique (C : LinearMap.BilinForm ℝ (_root_.DirectLimit V f))
    (hC : ∀ i (x y : V i),
      C (DirectLimit.Module.of ℝ I V f i x)
        (DirectLimit.Module.of ℝ I V f i y) = B i x y) :
    C = form f B hB := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  refine DirectLimit.induction₂ f (fun i a b => ?_) x y
  change C (DirectLimit.Module.of ℝ I V f i a)
      (DirectLimit.Module.of ℝ I V f i b) =
    form f B hB (DirectLimit.Module.of ℝ I V f i a)
      (DirectLimit.Module.of ℝ I V f i b)
  rw [hC i a b, form_of]

/-- Symmetry of every stage form gives symmetry of the descended form. -/
theorem form_isSymm (hSym : ∀ i, LinearMap.IsSymm (B i)) :
    LinearMap.IsSymm (form f B hB) := by
  refine ⟨?_⟩
  intro x y
  refine DirectLimit.induction₂ f (fun i a b => ?_) x y
  change form f B hB (DirectLimit.Module.of ℝ I V f i a)
      (DirectLimit.Module.of ℝ I V f i b) =
    form f B hB (DirectLimit.Module.of ℝ I V f i b)
      (DirectLimit.Module.of ℝ I V f i a)
  simp only [form_of]
  exact (hSym i).eq a b

/-- Nonnegativity of the limit form is exactly nonnegativity at every stage.
The canonical maps need not be injective. -/
theorem form_nonneg_iff :
    (∀ z, 0 ≤ form f B hB z z) ↔ ∀ i x, 0 ≤ B i x x := by
  constructor
  · intro h i x
    simpa only [form_of] using h (DirectLimit.Module.of ℝ I V f i x)
  · intro h z
    refine DirectLimit.induction f (fun i x => ?_) z
    change 0 ≤ form f B hB (DirectLimit.Module.of ℝ I V f i x)
      (DirectLimit.Module.of ℝ I V f i x)
    simpa only [form_of] using h i x

/-- A negative self-pairing survives in the limit and proves that its stage
image is nonzero, without requiring injectivity of the transition maps. -/
theorem negative_survives (i : I) (x : V i) (hx : B i x x < 0) :
    form f B hB (DirectLimit.Module.of ℝ I V f i x)
        (DirectLimit.Module.of ℝ I V f i x) < 0 ∧
      DirectLimit.Module.of ℝ I V f i x ≠ 0 := by
  have hneg : form f B hB (DirectLimit.Module.of ℝ I V f i x)
      (DirectLimit.Module.of ℝ I V f i x) < 0 := by
    simpa only [form_of] using hx
  refine ⟨hneg, ?_⟩
  intro hzero
  rw [hzero, map_zero] at hneg
  exact (lt_irrefl 0) hneg

end InfoGeometry.LinearAlgebra.DirectLimitBilinear

end

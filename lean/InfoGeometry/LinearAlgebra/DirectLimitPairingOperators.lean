/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LinearAlgebra.DirectLimitBilinear
import InfoGeometry.LinearAlgebra.DirectLimitEndomorphism
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Adjoint pairs and radical operators on a real directed limit

Compatible stage adjoint pairs descend for the actual bilinear form and
endomorphisms constructed on Mathlib's root direct limit. An adjoint relation
preserves the left radical `LinearMap.ker B`; native `Submodule.mapQ` therefore
constructs the induced endomorphism of the radical quotient.

Symmetry, positivity, injective transitions, and completion are not needed
for these algebraic statements. No boundedness or continuous extension of the
operators is asserted.
-/

noncomputable section

namespace InfoGeometry.LinearAlgebra.DirectLimitPairingOperators

open InfoGeometry.LinearAlgebra.DirectLimitBilinear
open InfoGeometry.LinearAlgebra.DirectLimitEndomorphism

/-- The first operator in a native adjoint pair preserves the left radical.
This does not require the bilinear form to be symmetric or nondegenerate. -/
theorem ker_le_comap_of_isAdjointPair
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (B : LinearMap.BilinForm ℝ W) (T S : W →ₗ[ℝ] W)
    (hAdj : LinearMap.IsAdjointPair B B T S) :
    LinearMap.ker B ≤ (LinearMap.ker B).comap T := by
  intro x hx
  change T x ∈ LinearMap.ker B
  rw [LinearMap.mem_ker] at hx ⊢
  apply LinearMap.ext
  intro y
  change B (T x) y = 0
  rw [hAdj x y, hx, LinearMap.zero_apply]

variable {I : Type*} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {V : I → Type*}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
variable (f : ∀ i j, i ≤ j → V i →ₗ[ℝ] V j)
variable [DirectedSystem V (fun i j h x => f i j h x)]
variable (B : ∀ i, LinearMap.BilinForm ℝ (V i))
variable (hB : ∀ i j (h : i ≤ j) (x y : V i),
  B j (f i j h x) (f i j h y) = B i x y)
variable (T S : ∀ i, V i →ₗ[ℝ] V i)
variable (hT : ∀ i j (h : i ≤ j) (x : V i),
  T j (f i j h x) = f i j h (T i x))
variable (hS : ∀ i j (h : i ≤ j) (x : V i),
  S j (f i j h x) = f i j h (S i x))
variable (hAdj : ∀ i, LinearMap.IsAdjointPair (B i) (B i) (T i) (S i))

include hAdj in
/-- Native adjoint-pair identities descend by putting both arguments at one
common stage and evaluating the constructed form and endomorphisms there. -/
theorem isAdjointPair_descendEnd :
    LinearMap.IsAdjointPair (form f B hB) (form f B hB)
      (descendEnd f T hT) (descendEnd f S hS) := by
  intro x y
  refine DirectLimit.induction₂ f (fun i a b => ?_) x y
  change form f B hB
      (descendEnd f T hT (DirectLimit.Module.of ℝ I V f i a))
      (DirectLimit.Module.of ℝ I V f i b) =
    form f B hB (DirectLimit.Module.of ℝ I V f i a)
      (descendEnd f S hS (DirectLimit.Module.of ℝ I V f i b))
  simp only [descendEnd_of, form_of]
  exact hAdj i a b

include S hS hAdj in
/-- The descended first operator preserves the radical of the constructed
limit form. This supplies the quotient-map premise rather than assuming it. -/
theorem descendEnd_preserves_radical :
    LinearMap.ker (form f B hB) ≤
      (LinearMap.ker (form f B hB)).comap (descendEnd f T hT) :=
  ker_le_comap_of_isAdjointPair (form f B hB)
    (descendEnd f T hT) (descendEnd f S hS)
    (isAdjointPair_descendEnd f B hB T S hT hS hAdj)

include S hS hAdj in
/-- The actual endomorphism on the native radical quotient, obtained from the
stage adjoint-pair data using `Submodule.mapQ`. -/
def quotientEnd :
    (_root_.DirectLimit V f ⧸ LinearMap.ker (form f B hB)) →ₗ[ℝ]
      (_root_.DirectLimit V f ⧸ LinearMap.ker (form f B hB)) :=
  (LinearMap.ker (form f B hB)).mapQ (LinearMap.ker (form f B hB))
    (descendEnd f T hT)
    (descendEnd_preserves_radical f B hB T S hT hS hAdj)

/-- The quotient operator sends the class of a vector to the class of its
descended image. -/
@[simp]
theorem quotientEnd_mk (x : _root_.DirectLimit V f) :
    quotientEnd f B hB T S hT hS hAdj (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (descendEnd f T hT x) :=
  rfl

/-- A stage vector has exactly the expected operator image after both native
direct-limit and radical-quotient descent. -/
@[simp]
theorem quotientEnd_of_mk (i : I) (x : V i) :
    quotientEnd f B hB T S hT hS hAdj
        (Submodule.Quotient.mk (DirectLimit.Module.of ℝ I V f i x)) =
      Submodule.Quotient.mk (DirectLimit.Module.of ℝ I V f i (T i x)) := by
  rw [quotientEnd_mk, descendEnd_of]

end InfoGeometry.LinearAlgebra.DirectLimitPairingOperators

end

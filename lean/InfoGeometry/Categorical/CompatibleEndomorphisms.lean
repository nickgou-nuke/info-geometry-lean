/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Module.LinearMap.End

/-!
# Compatible endomorphisms on algebraic directed colimits

Intertwining stage operators descend through Mathlib's native `DirectLimit`.
The bonds are hom-polymorphic, so linear and algebra homomorphisms retain the
same quotient carrier. Reflection identities descend by checking stage images.
Nonzero eigenvectors survive under the stated injectivity hypothesis on bonds.
-/

namespace InfoGeometry.Categorical.CompatibleEndomorphisms

noncomputable section

variable {R I : Type*} [Ring R] [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
variable {H : ∀ ⦃i j : I⦄, i ≤ j → Type*}
variable [∀ i j (h : i ≤ j), FunLike (H h) (V i) (V j)]
variable [∀ i j (h : i ≤ j), LinearMapClass (H h) R (V i) (V j)]
variable (f : ∀ i j (h : i ≤ j), H h) [DirectedSystem V (f · · ·)]

/-- A family intertwining every bond induces an endomorphism of the colimit. -/
def liftEnd (T : ∀ i, Module.End R (V i))
    (hT : ∀ i j h x, T j (f i j h x) = f i j h (T i x)) :
    Module.End R (_root_.DirectLimit V f) :=
  _root_.DirectLimit.Module.lift R I V f
    (fun i => (_root_.DirectLimit.Module.of R I V f i).comp (T i))
    (by
      intro i j h x
      change _root_.DirectLimit.Module.of R I V f j (T j (f i j h x)) =
        _root_.DirectLimit.Module.of R I V f i (T i x)
      rw [hT i j h x]
      exact _root_.DirectLimit.Module.of_f)

variable (T : ∀ i, Module.End R (V i))
variable (hT : ∀ i j h x, T j (f i j h x) = f i j h (T i x))

/-- The descended operator agrees with its prescribed action on each stage. -/
-- theorem-class: transport
@[simp] theorem liftEnd_of (i : I) (x : V i) :
    liftEnd f T hT (_root_.DirectLimit.Module.of R I V f i x) =
      _root_.DirectLimit.Module.of R I V f i (T i x) :=
  _root_.DirectLimit.Module.lift_of _ _ x

/-- A stagewise involution remains an involution on the entire colimit. -/
-- theorem-class: transport
theorem liftEnd_involution (hTT : ∀ i, T i * T i = 1) :
    liftEnd f T hT * liftEnd f T hT = 1 := by
  apply _root_.DirectLimit.Module.hom_ext
  intro i
  ext x
  change liftEnd f T hT (liftEnd f T hT
      (_root_.DirectLimit.Module.of R I V f i x)) =
    _root_.DirectLimit.Module.of R I V f i x
  rw [liftEnd_of, liftEnd_of]
  have hx := congrArg (fun S : Module.End R (V i) => S x) (hTT i)
  change T i (T i x) = x at hx
  rw [hx]

/-- The noncommutative reflection identity descends with both operators. -/
-- theorem-class: transport
theorem liftEnd_reflection (D : ∀ i, Module.End R (V i))
    (hD : ∀ i j h x, D j (f i j h x) = f i j h (D i x))
    (hTDT : ∀ i, T i * D i * T i = -D i) :
    liftEnd f T hT * liftEnd f D hD * liftEnd f T hT =
      -liftEnd f D hD := by
  apply _root_.DirectLimit.Module.hom_ext
  intro i
  ext x
  change liftEnd f T hT (liftEnd f D hD (liftEnd f T hT
      (_root_.DirectLimit.Module.of R I V f i x))) =
    -(liftEnd f D hD (_root_.DirectLimit.Module.of R I V f i x))
  rw [liftEnd_of, liftEnd_of, liftEnd_of, liftEnd_of]
  have hx := congrArg (fun S : Module.End R (V i) => S x) (hTDT i)
  change T i (D i (T i x)) = -(D i x) at hx
  rw [hx, map_neg]

/-- Eigen-equations descend even when the stage image could vanish. -/
-- theorem-class: transport
theorem liftEnd_eigen_equation {i : I} {x : V i} {a : R}
    (hx : T i x = a • x) :
    liftEnd f T hT (_root_.DirectLimit.Module.of R I V f i x) =
      a • _root_.DirectLimit.Module.of R I V f i x := by
  rw [liftEnd_of, hx, map_smul]

/-- Injective bonds preserve the nonzero part of an eigenpair as well. -/
-- theorem-class: transport
theorem liftEnd_eigenpair
    (hf : ∀ i j h, Function.Injective (f i j h))
    {i : I} {x : V i} {a : R} (hx : x ≠ 0) (hTx : T i x = a • x) :
    _root_.DirectLimit.Module.of R I V f i x ≠ 0 ∧
      liftEnd f T hT (_root_.DirectLimit.Module.of R I V f i x) =
        a • _root_.DirectLimit.Module.of R I V f i x := by
  constructor
  · have hi : Function.Injective (_root_.DirectLimit.Module.of R I V f i) :=
      _root_.DirectLimit.mk_injective f hf i
    simpa only [map_zero] using hi.ne hx
  · exact liftEnd_eigen_equation f T hT hTx

end

end InfoGeometry.Categorical.CompatibleEndomorphisms

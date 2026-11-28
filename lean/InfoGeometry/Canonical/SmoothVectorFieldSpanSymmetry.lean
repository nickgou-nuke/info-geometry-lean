/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SmoothDiffeomorphismPushforward
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Pointwise field symmetries and setwise preservation of their span

Derivative pushforward is real linear on the native field carrier `E → E`.
Consequently fixing every field in a family is equivalent to fixing every
field in its real span. This pointwise fixing subgroup is contained in the
setwise stabilizer of the span under the native action on sets.

Setwise stabilization permits nonidentity linear action within the span;
the converse inclusion is not asserted. No group normalizer is identified
with a vector-space span, and no regularity or flow-existence hypothesis is
imposed on the vector fields.
-/

noncomputable section

namespace InfoGeometry.Canonical.SmoothVectorFieldSpanSymmetry

open SmoothDiffeomorphismPushforward
open scoped Pointwise SmoothDiffeomorphismPushforward

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The image action on field families uses derivative pushforward, rather than
the ambient homeomorphism action available through subgroup restriction. -/
scoped instance (priority := 1100) vectorFieldSetSMul :
    SMul (smoothDiffeomorphismSubgroup E) (Set (E → E)) :=
  @Set.smulSet (smoothDiffeomorphismSubgroup E) (E → E) (vectorFieldSMul (E := E))

/-- Lift the specified field action to sets using Mathlib's native construction. -/
scoped instance (priority := 1100) vectorFieldSetAction :
    MulAction (smoothDiffeomorphismSubgroup E) (Set (E → E)) :=
  @Set.mulActionSet (smoothDiffeomorphismSubgroup E) (E → E) _
    (vectorFieldAction (E := E))

@[simp] theorem vectorFieldSet_smul_eq_image (g : smoothDiffeomorphismSubgroup E)
    (F : Set (E → E)) : g • F = pushforward g '' F := rfl

/-- Fixing a family of fields pointwise is equivalent to fixing its real span
pointwise, by the linearity of actual derivative pushforward. -/
theorem fixingSubgroup_span (F : Set (E → E)) :
    _root_.fixingSubgroup (smoothDiffeomorphismSubgroup E)
        (Submodule.span ℝ F : Set (E → E)) =
      _root_.fixingSubgroup (smoothDiffeomorphismSubgroup E) F := by
  ext g
  rw [_root_.mem_fixingSubgroup_iff, _root_.mem_fixingSubgroup_iff]
  change Set.EqOn (pushforwardLinearEquiv g).toLinearMap
      (LinearMap.id : (E → E) →ₗ[ℝ] (E → E)) (Submodule.span ℝ F : Set (E → E)) ↔
    Set.EqOn (pushforwardLinearEquiv g).toLinearMap
      (LinearMap.id : (E → E) →ₗ[ℝ] (E → E)) F
  exact LinearMap.eqOn_span_iff

/-- Pointwise preservation of the generating fields implies setwise
preservation of their real span. The target is the native set stabilizer. -/
theorem fixingSubgroup_le_stabilizer_span (F : Set (E → E)) :
    _root_.fixingSubgroup (smoothDiffeomorphismSubgroup E) F ≤
      MulAction.stabilizer (smoothDiffeomorphismSubgroup E)
        (Submodule.span ℝ F : Set (E → E)) := by
  intro g hg
  have hspan : g ∈ _root_.fixingSubgroup (smoothDiffeomorphismSubgroup E)
      (Submodule.span ℝ F : Set (E → E)) := by
    rwa [fixingSubgroup_span]
  have hfix : Set.EqOn (pushforward g) id (Submodule.span ℝ F : Set (E → E)) := by
    intro X hX
    exact (_root_.mem_fixingSubgroup_iff (smoothDiffeomorphismSubgroup E)).mp hspan X hX
  rw [MulAction.mem_stabilizer_iff, vectorFieldSet_smul_eq_image]
  exact hfix.image_eq_self

end InfoGeometry.Canonical.SmoothVectorFieldSpanSymmetry

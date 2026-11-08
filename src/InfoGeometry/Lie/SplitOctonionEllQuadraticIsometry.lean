/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Lie.SplitOctonionEllClosedFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionErlangenInvariant

/-!
# Quadratic isometry of the projector-derived ell flow

This owner reuses the canonical quadratic map built from the native Zorn
determinant.  It promotes the already proved determinant preservation of the
closed `ell` flow to Mathlib's genuine `QuadraticMap.IsometryEquiv` API.
No multiplication-preservation or `G₂` claim is made.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllQuadraticIsometry

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionEllClosedFlow
open InfoGeometry.Lie.SplitOctonionErlangenInvariant

abbrev CZ := CanonicalZorn

/-- The closed projector-derived `ell` flow as a quadratic isometry of the
native determinant form. -/
def ellFlowPhiQuadraticIsometry (t : ℝ) :
    canonicalDetQuadratic.IsometryEquiv canonicalDetQuadratic :=
  { ellFlowPhiEquiv t with
    map_app' := fun X => by
      exact ellFlowPhi_preserves_det t X }

@[simp] theorem ellFlowPhiQuadraticIsometry_apply (t : ℝ) (X : CZ) :
    ellFlowPhiQuadraticIsometry t X = ellFlowPhi t X :=
  rfl

@[simp] theorem ellFlowPhiQuadraticIsometry_preserves_form
    (t : ℝ) (X : CZ) :
    canonicalDetQuadratic (ellFlowPhiQuadraticIsometry t X) =
      canonicalDetQuadratic X := by
  exact QuadraticMap.IsometryEquiv.map_app
    (ellFlowPhiQuadraticIsometry t) X

theorem ellFlowPhiQuadraticIsometry_preserves_det
    (t : ℝ) (X : CZ) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3
        (ellFlowPhiQuadraticIsometry t X) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realCrossProduct3 X := by
  simpa [ellFlowPhiQuadraticIsometry_apply] using
    (ellFlowPhi_preserves_det t X)

theorem isometryEquiv_ext
    {f g : canonicalDetQuadratic.IsometryEquiv canonicalDetQuadratic}
    (h : f.toLinearEquiv = g.toLinearEquiv) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      dsimp at h
      cases h
      rfl

theorem ellFlowPhiQuadraticIsometry_trans (s t : ℝ) :
    (ellFlowPhiQuadraticIsometry s).trans (ellFlowPhiQuadraticIsometry t) =
      ellFlowPhiQuadraticIsometry (s + t) := by
  apply isometryEquiv_ext
  apply LinearEquiv.ext
  intro X
  change ellFlowPhi t (ellFlowPhi s X) = ellFlowPhi (s + t) X
  rw [← Module.End.mul_apply, ← ellFlowPhi_add]
  rw [add_comm]

theorem ellFlowPhiQuadraticIsometry_symm (t : ℝ) :
    (ellFlowPhiQuadraticIsometry t).symm =
      ellFlowPhiQuadraticIsometry (-t) := by
  apply isometryEquiv_ext
  apply LinearEquiv.ext
  intro X
  change ellFlowPhi (-t) X = ellFlowPhi (-t) X
  rfl

end InfoGeometry.Lie.SplitOctonionEllQuadraticIsometry

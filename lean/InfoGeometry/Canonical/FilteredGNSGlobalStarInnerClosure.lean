/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.FilteredGNSGlobalStageRepresentation
import InfoGeometry.Canonical.FilteredGNSTailStarRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Wave 5 candidate: global GNS adjoint pairing

The global stage representation is obtained by unitary transport from a
cofinal-tail representation.  The existing owners prove the tail adjoint
pairing and the global representation formula, but do not expose the
corresponding inner-product identity for arbitrary vectors of the global
Hilbert colimit.  This file adds that operator-level transport theorem.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSTailRepresentation
open CStarStateColimit.Native.FilteredGNSTailStarRepresentation
open CStarStateColimit.Native.FilteredGNSCofinalTail
open InfoGeometry.Canonical.FilteredIsometricInnerProductColimit
open InfoGeometry.Canonical.FilteredIsometricHilbertCompletion

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable [DecidableEq I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      Stage sys)

/-- The global GNS representation transports the tail Hilbert-adjoint pairing
through the canonical cofinal-tail unitary, for arbitrary global vectors. -/
theorem globalStageRepresentation_star_inner
    {i₀ : I} (a : Stage i₀)
    (z w : GNSHilbertColimit Stage sys ω) :
    inner ℂ
        (globalStageRepresentationStarAlgHom Stage sys ω i₀ (star a) w) z =
      inner ℂ w
        (globalStageRepresentationStarAlgHom Stage sys ω i₀ a z) := by
  obtain ⟨z', rfl⟩ :=
    (tailHilbertGlobalEquiv Stage sys ω i₀).surjective z
  obtain ⟨w', rfl⟩ :=
    (tailHilbertGlobalEquiv Stage sys ω i₀).surjective w
  rw [globalStageRepresentation_apply,
    globalStageRepresentation_apply]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  calc
    inner ℂ
        (tailHilbertGlobalEquiv Stage sys ω i₀
          (tailCompletedRepresentation Stage sys ω (star a) w'))
        (tailHilbertGlobalEquiv Stage sys ω i₀ z') =
      inner ℂ
        (tailCompletedRepresentation Stage sys ω (star a) w') z' :=
      (tailHilbertGlobalEquiv Stage sys ω i₀).inner_map_map _ _
    _ = inner ℂ w'
        (tailCompletedRepresentation Stage sys ω a z') :=
      tailCompletedRepresentation_star_inner Stage sys ω a z' w'
    _ = inner ℂ
        (tailHilbertGlobalEquiv Stage sys ω i₀ w')
        (tailHilbertGlobalEquiv Stage sys ω i₀
          (tailCompletedRepresentation Stage sys ω a z')) :=
      ((tailHilbertGlobalEquiv Stage sys ω i₀).inner_map_map _ _).symm

end CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredGNSTomitaClosability
import InfoGeometry.OperatorAlgebra.TracialGNSRightMultiplication

/-!
# Closability of the native tracial GNS Tomita core

The norm estimate on the actual pre-GNS carrier controls the closure of its
graph.  Trace cyclicity supplies that estimate with constant one, so closability
is proved rather than supplied as a field.  The carrier is Mathlib's seminormed
pre-GNS space and its existing separated Hilbert completion throughout.
-/

noncomputable section

namespace CStarStateColimit.Native.TracialGNSTomitaClosability

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSTomitaCore
open CStarStateColimit.Native.FilteredGNSTomitaGraph
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open Set

universe u

variable {A : Type u}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A genuine bound on the dense Tomita core implies that its closed graph has
trivial vertical kernel.  No normed instance on pre-GNS is needed. -/
theorem isClosableTomitaCore_of_norm_bound
    (ω : State A) (C : ℝ)
    (hbound : ∀ x : ω.functional.PreGNS,
      ‖tomitaCore ω x‖ ≤ C * ‖x‖) :
    IsClosableTomitaCore ω := by
  let R : Set (ω.functional.GNS × ω.functional.GNS) :=
    {p | ‖p.2‖ ≤ C * ‖p.1‖}
  have hR : IsClosed R :=
    isClosed_le continuous_snd.norm (continuous_const.mul continuous_fst.norm)
  have hgraph : tomitaCoreGraph ω ⊆ R := by
    rintro p ⟨x, rfl⟩
    simpa only [R, mem_setOf_eq, UniformSpace.Completion.norm_coe] using hbound x
  have hclosed : closedTomitaCoreGraph ω ⊆ R :=
    closure_minimal hgraph hR
  intro η hη
  have hnorm : ‖η‖ ≤ 0 := by
    simpa only [R, mem_setOf_eq, norm_zero, mul_zero] using hclosed hη
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg η))

/-- The native tracial Tomita core preserves the pre-GNS seminorm. -/
theorem tomitaCore_norm_of_tracial
    (ω : State A)
    (htr : ∀ a b : A, ω.functional (a * b) = ω.functional (b * a))
    (x : ω.functional.PreGNS) :
    ‖tomitaCore ω x‖ = ‖x‖ := by
  obtain ⟨a, rfl⟩ := ω.functional.toPreGNS.surjective x
  rw [tomitaCore_toPreGNS]
  exact ω.functional.tracial_preGNS_star_norm htr a

/-- Trace cyclicity discharges the existing Tomita closability criterion. -/
theorem isClosableTomitaCore_of_tracial
    (ω : State A)
    (htr : ∀ a b : A, ω.functional (a * b) = ω.functional (b * a)) :
    IsClosableTomitaCore ω := by
  apply isClosableTomitaCore_of_norm_bound ω 1
  intro x
  rw [tomitaCore_norm_of_tracial ω htr, one_mul]

end CStarStateColimit.Native.TracialGNSTomitaClosability

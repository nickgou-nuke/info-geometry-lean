/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.TracialGNSTomitaClosability
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Finite faithful states have closable native Tomita cores

Faithfulness proves separation of the original pre-GNS seminorm.  Only then is
the same seminorm promoted locally to a norm.  Finite dimensionality makes the
actual real-linear star operation bounded; the existing graph criterion gives
closability.  Faithfulness is essential and is not replaced by representation
injectivity or by an assumption that the desired closed graph is single-valued.
-/

noncomputable section

namespace CStarStateColimit.Native.FiniteFaithfulGNSTomitaClosability

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSTomitaCore
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open CStarStateColimit.Native.TracialGNSTomitaClosability

universe u

variable {A : Type u}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Faithfulness of the positive functional separates its native pre-GNS
seminorm.  This lemma does not assume a normed pre-GNS carrier. -/
theorem preGNS_eq_zero_of_norm_eq_zero_of_faithful
    (ω : State A)
    (hfaith : ∀ a : A, ω.functional (star a * a) = 0 → a = 0)
    (x : ω.functional.PreGNS) (hx : ‖x‖ = 0) : x = 0 := by
  have hs := ω.functional.preGNS_norm_sq x
  have hval : ω.functional
      (star (ω.functional.ofPreGNS x) * ω.functional.ofPreGNS x) = 0 := by
    simpa only [hx, Complex.ofReal_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      using hs.symm
  have ha := hfaith (ω.functional.ofPreGNS x) hval
  calc
    x = ω.functional.toPreGNS (ω.functional.ofPreGNS x) := by simp
    _ = 0 := by rw [ha, map_zero]

/-- Restricting the existing conjugate-linear core to real scalars gives a
genuine linear map on the same pre-GNS carrier. -/
def tomitaCoreRealLinearMap (ω : State A) :
    ω.functional.PreGNS →ₗ[ℝ] ω.functional.PreGNS where
  toFun := tomitaCore ω
  map_add' := tomitaCore_add ω
  map_smul' := by
    intro r x
    simpa using tomitaCore_smul ω (r : ℂ) x

/-- A faithful state on a finite-dimensional C⋆ algebra has a closable Tomita
core.  Its dense-core bound is derived from finite-dimensional continuity. -/
theorem isClosableTomitaCore_of_finiteDimensional_faithful
    [FiniteDimensional ℂ A]
    (ω : State A)
    (hfaith : ∀ a : A, ω.functional (star a * a) = 0 → a = 0) :
    IsClosableTomitaCore ω := by
  letI : NormedAddCommGroup ω.functional.PreGNS :=
    NormedAddCommGroup.ofSeparation
      (preGNS_eq_zero_of_norm_eq_zero_of_faithful ω hfaith)
  letI : FiniteDimensional ℂ ω.functional.PreGNS :=
    ω.functional.toPreGNS.finiteDimensional
  letI : FiniteDimensional ℝ ω.functional.PreGNS :=
    FiniteDimensional.trans ℝ ℂ ω.functional.PreGNS
  let T : ω.functional.PreGNS →L[ℝ] ω.functional.PreGNS :=
    ⟨tomitaCoreRealLinearMap ω,
      (tomitaCoreRealLinearMap ω).continuous_of_finiteDimensional⟩
  apply isClosableTomitaCore_of_norm_bound ω ‖T‖
  intro x
  exact T.le_opNorm x

end CStarStateColimit.Native.FiniteFaithfulGNSTomitaClosability

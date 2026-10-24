/- SPDX-License-Identifier: Apache-2.0 -/
import InfoGeometry.Canonical.FilteredGNSVacuumState
import InfoGeometry.Canonical.FiniteSeedGibbsCStarStates
import InfoGeometry.Canonical.AlgebraicKMSStateColimitReadback

/-! Finite nontraciality survives in the actual represented completed state.
No faithfulness assumption is required: state readback itself preserves the
scalar inequality. No new carrier or completed-state witness is postulated. -/
noncomputable section
namespace CStarStateColimit.Native.FilteredGNSNontracialReadback

open CStarStateColimit.Native
open FilteredGNSGlobalStageRepresentation FilteredGNSRepresentedCStarClosure
open FilteredGNSVacuumState

universe u
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

/-- An actual finite product inequality refutes global cyclicity of the
constructed state on the represented C⋆ closure. -/
theorem representedVacuumState_not_tracial (v i : I) (a b : Stage i)
    (hab : (ω.state i).functional (a * b) ≠ (ω.state i).functional (b * a)) :
    ¬ ∀ A B : representedCStarClosure Stage sys ω,
      (representedVacuumState Stage sys ω v).functional (A * B) =
        (representedVacuumState Stage sys ω v).functional (B * A) := by
  intro h
  let f : Stage i →⋆ₐ[ℂ] representedCStarClosure Stage sys ω :=
    (globalStageRepresentationStarAlgHom Stage sys ω i).codRestrict
      (representedCStarClosure Stage sys ω)
      (globalStageRepresentation_mem_representedCStarClosure Stage sys ω i)
  have hf (x : Stage i) :
      (representedVacuumState Stage sys ω v).functional (f x) =
        (ω.state i).functional x := by
    exact representedVacuumState_stage Stage sys ω v i x
  have he := h (f a) (f b)
  rw [← map_mul, ← map_mul, hf, hf] at he
  exact hab he

end CStarStateColimit.Native.FilteredGNSNontracialReadback

namespace InfoGeometry.Canonical.AlgebraicKMSStateColimit

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSVacuumState
open CStarStateColimit.Native.FilteredGNSNontracialReadback
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

/-- A seed matrix witness propagates to the actual completed vacuum state of
the native finite-seed compatible C⋆ state family, for any vacuum-stage choice. -/
theorem finiteSeed_representedVacuumState_not_tracial {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ)
    (a b : MatrixStage k)
    (hab : gibbsFunctional H hH β (a * b) ≠ gibbsFunctional H hH β (b * a))
    (v : ℕ) :
    ¬ ∀ A B : representedCStarClosure CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β),
      (representedVacuumState CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β) v).functional (A * B) =
      (representedVacuumState CStarMatrixStage cstarMatrixInductiveSystem
        (finiteSeedCompatibleStageStates H hH β) v).functional (B * A) := by
  let e : MatrixStage k ≃⋆ₐ[ℂ] CStarMatrixStage k := CStarMatrix.ofMatrixStarAlgEquiv
  have hr (x : MatrixStage k) :
      ((finiteSeedCompatibleStageStates H hH β).state k).functional (e x) =
        gibbsFunctional H hH β x := by
    change (finiteSeedStageState H hH β k).functional (e x) = _
    rw [finiteSeedStageState_apply]
    simp only [e, StarAlgEquiv.symm_apply_apply]
    exact normalizedDeltaWeightedFunctional_stage_eq_gibbsFunctional H hH β x
  have he : ((finiteSeedCompatibleStageStates H hH β).state k).functional (e a * e b) ≠
      ((finiteSeedCompatibleStageStates H hH β).state k).functional (e b * e a) := by
    rw [← map_mul, ← map_mul, hr, hr]
    exact hab
  exact representedVacuumState_not_tracial CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates H hH β) v k (e a) (e b) he

end InfoGeometry.Canonical.AlgebraicKMSStateColimit

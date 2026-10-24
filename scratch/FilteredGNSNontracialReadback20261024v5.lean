/- SPDX-License-Identifier: Apache-2.0 -/
import InfoGeometry.Canonical.FilteredGNSVacuumState
import InfoGeometry.Canonical.FiniteSeedGibbsCStarStates
import InfoGeometry.Canonical.AlgebraicKMSStateColimitReadback

/-! Finite nontraciality survives in the actual represented completed state.
No faithfulness assumption is required: state readback itself preserves the
scalar inequality. No new carrier or completed-state witness is postulated. -/
noncomputable section
open scoped ComplexOrder
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000
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

attribute [local instance]
  CStarStateColimit.Native.FilteredGNSVacuumState.representedSpectralOrder
  CStarStateColimit.Native.FilteredGNSVacuumState.representedSpectralStarOrderedRing

/-- An actual finite product inequality refutes global cyclicity of the
constructed state on the represented C⋆ closure. -/
theorem representedVacuumState_not_tracial (v i : I) (a b : Stage i)
    (hab : (ω.state i).functional (a * b) ≠ (ω.state i).functional (b * a)) :
    let ρ := representedVacuumState Stage sys ω v
    ¬ ∀ A B : representedCStarClosure Stage sys ω,
      ρ.functional (A * B) = ρ.functional (B * A) := by
  dsimp only
  intro h
  let f : Stage i →⋆ₐ[ℂ] representedCStarClosure Stage sys ω :=
    (globalStageRepresentationStarAlgHom Stage sys ω i).codRestrict
      (representedCStarClosure Stage sys ω)
      (globalStageRepresentation_mem_representedCStarClosure Stage sys ω i)
  have hf (x : Stage i) :
      (representedVacuumState Stage sys ω v).functional (f x) =
        (ω.state i).functional x := by
    exact representedVacuumState_stage Stage sys ω v i x
  let ψ : representedCStarClosure Stage sys ω → ℂ :=
    fun x => (representedVacuumState Stage sys ω v).functional x
  have hab_map : ψ (f (a * b)) = ψ (f a * f b) :=
    congrArg ψ (map_mul f a b)
  have hba_map : ψ (f (b * a)) = ψ (f b * f a) :=
    congrArg ψ (map_mul f b a)
  exact hab ((hf (a * b)).symm.trans
    (hab_map.trans ((h (f a) (f b)).trans
      (hba_map.symm.trans (hf (b * a))))))

end CStarStateColimit.Native.FilteredGNSNontracialReadback

namespace InfoGeometry.Canonical.AlgebraicKMSStateColimit

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CStarStateColimit.Native.FilteredGNSVacuumState
open CStarStateColimit.Native.FilteredGNSNontracialReadback
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open InfoGeometry.Canonical.FiniteMatrixGibbsFunctional

/-- Expose Mathlib's existing instances at the dependent-family type. -/
private abbrev matrixStageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun n => (inferInstance : CStarAlgebra (CStarMatrixStage n))

private abbrev matrixStageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun n => (inferInstance : PartialOrder (CStarMatrixStage n))

private abbrev matrixStageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun n => (inferInstance : StarOrderedRing (CStarMatrixStage n))

attribute [local instance] matrixStageCStarFamily matrixStageOrderFamily
  matrixStageStarOrderFamily

attribute [local instance]
  CStarStateColimit.Native.FilteredGNSVacuumState.representedSpectralOrder
  CStarStateColimit.Native.FilteredGNSVacuumState.representedSpectralStarOrderedRing

-- V4 exhausted 1M heartbeats normalizing the concrete dependent state header.
-- Keep the larger finite budget local to this one declaration.
set_option maxHeartbeats 4000000 in
/-- A seed matrix witness propagates to the actual completed vacuum state of
the native finite-seed compatible C⋆ state family, for any vacuum-stage choice. -/
theorem finiteSeed_representedVacuumState_not_tracial {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ)
    (a b : MatrixStage k)
    (hab : gibbsFunctional H hH β (a * b) ≠ gibbsFunctional H hH β (b * a))
    (v : ℕ) :
    let ωseed := finiteSeedCompatibleStageStates H hH β
    let ρ := representedVacuumState CStarMatrixStage cstarMatrixInductiveSystem ωseed v
    ¬ ∀ A B : representedCStarClosure CStarMatrixStage cstarMatrixInductiveSystem ωseed,
      ρ.functional (A * B) = ρ.functional (B * A) := by
  dsimp only
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
    intro heq
    let ψ : CStarMatrixStage k → ℂ :=
      fun x => ((finiteSeedCompatibleStageStates H hH β).state k).functional x
    have hab_map : ψ (e (a * b)) = ψ (e a * e b) :=
      congrArg ψ (map_mul e a b)
    have hba_map : ψ (e (b * a)) = ψ (e b * e a) :=
      congrArg ψ (map_mul e b a)
    exact hab ((hr (a * b)).symm.trans
      (hab_map.trans (heq.trans (hba_map.symm.trans (hr (b * a))))))
  exact representedVacuumState_not_tracial CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates H hH β) v k (e a) (e b) he

end InfoGeometry.Canonical.AlgebraicKMSStateColimit

/- SPDX-License-Identifier: Apache-2.0 -/
import InfoGeometry.Canonical.FilteredGNSRepresentedCStarClosure
import InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum
import Mathlib.Analysis.InnerProductSpace.Positive

/-! Vacuum readback on the existing represented closure. This constructs a
bounded normalized vector functional with proved star-square positivity,
without postulating an order on the closure or packaging a new State. -/
noncomputable section
namespace CStarStateColimit.Native.FilteredGNSVacuumReadback

open CStarStateColimit.Native
open FilteredGNS FilteredGNSHilbertColimit FilteredGNSHilbertNontrivial
open FilteredGNSTailRepresentation FilteredGNSGlobalStageRepresentation
open FilteredGNSRepresentedCStarClosure
open InfoGeometry.OperatorAlgebra.PositiveLinearMapGNSVacuum
open scoped InnerProductSpace ComplexOrder

universe u
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
variable (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)

theorem globalGNSVacuum_norm (i : I) :
    ‖globalGNSVacuum Stage sys ω i‖ = 1 := by
  unfold globalGNSVacuum
  rw [(gnsStageToHilbertColimit Stage sys ω i).norm_map]
  exact gnsVacuum_norm_eq_one (ω.state i).functional (ω.state i).normalized

theorem globalGNSVacuum_transition {i j : I} (hij : i ≤ j) :
    globalGNSVacuum Stage sys ω j = globalGNSVacuum Stage sys ω i := by
  have h := gnsStageToHilbertColimit_transition Stage sys ω hij
    ((ω.state i).functional.toPreGNS 1 : (ω.state i).functional.GNS)
  simpa only [filteredGNSMap_toPreGNS, map_one, globalGNSVacuum] using h

theorem globalGNSVacuum_eq (i j : I) :
    globalGNSVacuum Stage sys ω i = globalGNSVacuum Stage sys ω j := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  exact (globalGNSVacuum_transition Stage sys ω hik).symm.trans
    (globalGNSVacuum_transition Stage sys ω hjk)

theorem globalGNSVacuum_stage_expectation (i : I) (a : Stage i) :
    ⟪globalGNSVacuum Stage sys ω i,
      globalStageRepresentationStarAlgHom Stage sys ω i a
        (globalGNSVacuum Stage sys ω i)⟫_ℂ = (ω.state i).functional a := by
  unfold globalGNSVacuum
  rw [globalStageRepresentation_stage Stage sys ω a ⟨i, le_refl i⟩,
    (gnsStageToHilbertColimit Stage sys ω i).inner_map_map]
  simpa only [tailGNSOperator, tailObservable, sys.map_id, StarAlgHom.id_apply] using
    gns_state_expectation_recovery (ω.state i).functional a

/-- Evaluation on the actual closed operator subalgebra, not a new carrier. -/
def representedVacuumFunctional (i : I) :
    representedCStarClosure Stage sys ω →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟪globalGNSVacuum Stage sys ω i,
        (a : GNSHilbertColimit Stage sys ω →L[ℂ] GNSHilbertColimit Stage sys ω)
          (globalGNSVacuum Stage sys ω i)⟫_ℂ
      map_add' := by intros; simp [inner_add_right]
      map_smul' := by intros; simp [inner_smul_right] }
    1 (by
      intro a
      have hn := globalGNSVacuum_norm Stage sys ω i
      calc
        _ ≤ ‖globalGNSVacuum Stage sys ω i‖ *
            ‖(a : GNSHilbertColimit Stage sys ω →L[ℂ] GNSHilbertColimit Stage sys ω)
              (globalGNSVacuum Stage sys ω i)‖ := norm_inner_le_norm _ _
        _ ≤ ‖globalGNSVacuum Stage sys ω i‖ *
            (‖(a : GNSHilbertColimit Stage sys ω →L[ℂ] GNSHilbertColimit Stage sys ω)‖ *
              ‖globalGNSVacuum Stage sys ω i‖) :=
          mul_le_mul_of_nonneg_left ((a : GNSHilbertColimit Stage sys ω →L[ℂ]
            GNSHilbertColimit Stage sys ω).le_opNorm _) (norm_nonneg _)
        _ = 1 * ‖a‖ := by simp [hn])

theorem representedVacuumFunctional_one (i : I) :
    representedVacuumFunctional Stage sys ω i 1 = 1 := by
  change ⟪globalGNSVacuum Stage sys ω i, globalGNSVacuum Stage sys ω i⟫_ℂ = 1
  rw [inner_self_eq_norm_sq_to_K, globalGNSVacuum_norm]
  norm_num

/-- Positivity is derived from the concrete Hilbert adjoint. -/
theorem representedVacuumFunctional_star_mul_self (i : I)
    (a : representedCStarClosure Stage sys ω) :
    0 ≤ representedVacuumFunctional Stage sys ω i (star a * a) := by
  change 0 ≤ ⟪globalGNSVacuum Stage sys ω i,
    (star (a : GNSHilbertColimit Stage sys ω →L[ℂ] GNSHilbertColimit Stage sys ω))
      ((a : GNSHilbertColimit Stage sys ω →L[ℂ] GNSHilbertColimit Stage sys ω)
        (globalGNSVacuum Stage sys ω i))⟫_ℂ
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg

theorem representedVacuumFunctional_stage (i j : I) (a : Stage j) :
    representedVacuumFunctional Stage sys ω i
      ⟨globalStageRepresentationStarAlgHom Stage sys ω j a,
        globalStageRepresentation_mem_representedCStarClosure Stage sys ω j a⟩ =
      (ω.state j).functional a := by
  change ⟪globalGNSVacuum Stage sys ω i,
    globalStageRepresentationStarAlgHom Stage sys ω j a
      (globalGNSVacuum Stage sys ω i)⟫_ℂ = _
  rw [globalGNSVacuum_eq Stage sys ω i j]
  exact globalGNSVacuum_stage_expectation Stage sys ω j a

end CStarStateColimit.Native.FilteredGNSVacuumReadback

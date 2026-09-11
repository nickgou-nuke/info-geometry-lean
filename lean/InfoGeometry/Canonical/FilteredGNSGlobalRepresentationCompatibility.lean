import InfoGeometry.Canonical.FilteredGNSGlobalStageRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Transition compatibility of global filtered GNS representations

The representation obtained from a stage observable is independent of the
chosen later stage representing that observable.  This file proves that the
global stage representations commute strictly with every transition map of
the continuous star-inductive system.

The proof is genuinely filtered: an arbitrary test vector and the two
observable stages are transported to a common upper stage, where the native
GNS action and functoriality of the algebra transitions identify the two
operators.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSGlobalRepresentationCompatibility

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSTailRepresentation
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation

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

/-- Bounded operators on the global GNS Hilbert colimit are determined by
their values on every canonical stage image. -/
theorem globalContinuousLinearMap_eq_of_stage_eq
    {T U :
      GNSHilbertColimit Stage sys ω →L[ℂ]
        GNSHilbertColimit Stage sys ω}
    (h :
      ∀ (i : I) (x : (ω.state i).functional.GNS),
        T (gnsStageToHilbertColimit Stage sys ω i x) =
          U (gnsStageToHilbertColimit Stage sys ω i x)) :
    T = U := by
  apply ContinuousLinearMap.ext
  have hfun :
      (T : GNSHilbertColimit Stage sys ω →
        GNSHilbertColimit Stage sys ω) = U := by
    apply Continuous.ext_on
      (dense_iUnion_range_gnsStageToHilbertColimit
        Stage sys ω)
      T.continuous U.continuous
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
    rcases hi with ⟨x, rfl⟩
    exact h i x
  exact fun x => congrFun hfun x

/-- A stage observable and every later representative induce exactly the
same bounded operator on the global filtered GNS Hilbert colimit. -/
theorem globalStageRepresentation_transition
    {i j : I} (hij : i ≤ j) (a : Stage i) :
    globalStageRepresentationStarAlgHom Stage sys ω j
        (sys.map hij a) =
      globalStageRepresentationStarAlgHom Stage sys ω i a := by
  apply globalContinuousLinearMap_eq_of_stage_eq Stage sys ω
  intro k x
  obtain ⟨m, hkm, hjm⟩ := exists_ge_ge k j
  have him : i ≤ m := le_trans hij hjm
  let xm := filteredGNSMap Stage sys ω hkm x
  have hx :
      gnsStageToHilbertColimit Stage sys ω m xm =
        gnsStageToHilbertColimit Stage sys ω k x :=
    gnsStageToHilbertColimit_transition
      Stage sys ω hkm x
  rw [← hx]
  rw [globalStageRepresentation_stage
      Stage sys ω (sys.map hij a) ⟨m, hjm⟩ xm,
    globalStageRepresentation_stage
      Stage sys ω a ⟨m, him⟩ xm]
  congr 1
  unfold tailGNSOperator tailObservable
  have hmap :
      sys.map hjm (sys.map hij a) =
        sys.map him a := by
    exact congrArg
      (fun f : Stage i →⋆ₐ[ℂ] Stage m => f a)
      (sys.map_comp hij hjm)
  rw [hmap]

end CStarStateColimit.Native.FilteredGNSGlobalRepresentationCompatibility

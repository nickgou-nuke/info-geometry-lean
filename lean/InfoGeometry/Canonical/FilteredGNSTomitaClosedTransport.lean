import InfoGeometry.Canonical.FilteredGNSTomitaClosedOperator
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Filtered transport of closed Tomita operators

The filtered completed-GNS transitions already transport the closures of the
algebraic Tomita graphs.  Consequently they transport the projected closed
domains.  This file bundles those domain maps as complex-linear maps, proves
their identity and composition laws, and proves that they intertwine the
closed conjugate-linear Tomita operators whenever the source and target cores
are closable.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTomitaClosedTransport

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSTomitaGraph
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open CStarStateColimit.Native.FilteredGNSTomitaClosedOperator

universe u

variable {I : Type u} [Preorder I]
variable (Stage : I → Type u)
variable [∀ i, CStarAlgebra (Stage i)]
variable [∀ i, PartialOrder (Stage i)]
variable [∀ i, StarOrderedRing (Stage i)]
variable (sys : ContinuousStarInductiveSystem Stage)
variable
  (ω :
    ContinuousStarInductiveSystem.CompatibleStateFamily
      Stage sys)

/-- A filtered GNS transition maps the closed Tomita domain at the source
stage into the closed Tomita domain at the target stage. -/
theorem filteredGNSMap_mem_closedTomitaDomain
    {i j : I} (hij : i ≤ j)
    (x : closedTomitaDomain (ω.state i)) :
    filteredGNSMap Stage sys ω hij x.1 ∈
      closedTomitaDomain (ω.state j) := by
  obtain ⟨η, hη⟩ := x.property
  refine
    ⟨filteredGNSMap Stage sys ω hij η, ?_⟩
  exact
    filteredGNSPairMap_mapsTo_closedTomitaCoreGraph
      Stage sys ω hij hη

/-- Bundled complex-linear transport between the projected closed Tomita
domains. -/
def filteredClosedTomitaDomainMap
    {i j : I} (hij : i ≤ j) :
    closedTomitaDomain (ω.state i) →ₗ[ℂ]
      closedTomitaDomain (ω.state j) where
  toFun := fun x =>
    ⟨filteredGNSMap Stage sys ω hij x.1,
      filteredGNSMap_mem_closedTomitaDomain
        Stage sys ω hij x⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    change
      filteredGNSMap Stage sys ω hij
          (x.1 + y.1) =
        filteredGNSMap Stage sys ω hij x.1 +
          filteredGNSMap Stage sys ω hij y.1
    simpa only [filteredGNSMapCLM_apply] using
      (filteredGNSMapCLM Stage sys ω hij).map_add
        x.1 y.1
  map_smul' := by
    intro c x
    apply Subtype.ext
    change
      filteredGNSMap Stage sys ω hij
          (c • x.1) =
        c • filteredGNSMap Stage sys ω hij x.1
    simpa only [filteredGNSMapCLM_apply] using
      (filteredGNSMapCLM Stage sys ω hij).map_smul
        c x.1

@[simp] theorem filteredClosedTomitaDomainMap_apply
    {i j : I} (hij : i ≤ j)
    (x : closedTomitaDomain (ω.state i)) :
    (filteredClosedTomitaDomainMap
      Stage sys ω hij x).1 =
      filteredGNSMap Stage sys ω hij x.1 :=
  rfl

/-- Identity coherence of filtered closed-domain transport. -/
theorem filteredClosedTomitaDomainMap_id
    (i : I) :
    filteredClosedTomitaDomainMap
        Stage sys ω (le_refl i) =
      LinearMap.id := by
  ext x
  change
    filteredGNSMap Stage sys ω (le_refl i) x.1 =
      x.1
  exact congrFun
    (filteredGNSMap_id Stage sys ω i) x.1

/-- Composition coherence of filtered closed-domain transport. -/
theorem filteredClosedTomitaDomainMap_comp
    {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k) :
    (filteredClosedTomitaDomainMap
        Stage sys ω hjk).comp
        (filteredClosedTomitaDomainMap
          Stage sys ω hij) =
      filteredClosedTomitaDomainMap
        Stage sys ω (le_trans hij hjk) := by
  ext x
  change
    filteredGNSMap Stage sys ω hjk
        (filteredGNSMap Stage sys ω hij x.1) =
      filteredGNSMap Stage sys ω
        (le_trans hij hjk) x.1
  exact congrFun
    (filteredGNSMap_comp
      Stage sys ω hij hjk) x.1

/-- Closed graph transport sends the graph value at the source stage to a
graph value at the target stage. -/
theorem filteredGNSMap_closedTomitaValue_mem_graph
    {i j : I} (hij : i ≤ j)
    (x : closedTomitaDomain (ω.state i)) :
    (filteredGNSMap Stage sys ω hij x.1,
      filteredGNSMap Stage sys ω hij
        (closedTomitaValue (ω.state i) x)) ∈
      closedTomitaCoreGraph (ω.state j) := by
  exact
    filteredGNSPairMap_mapsTo_closedTomitaCoreGraph
      Stage sys ω hij
      (closedTomitaValue_mem_graph (ω.state i) x)

/-- Filtered GNS transport intertwines the closed conjugate-linear Tomita
operators. -/
theorem filteredGNSMap_intertwines_closedTomitaOperator
    {i j : I} (hij : i ≤ j)
    (hclos_i : IsClosableTomitaCore (ω.state i))
    (hclos_j : IsClosableTomitaCore (ω.state j))
    (x : closedTomitaDomain (ω.state i)) :
    filteredGNSMap Stage sys ω hij
        (closedTomitaOperator
          (ω.state i) hclos_i x) =
      closedTomitaOperator
        (ω.state j) hclos_j
        (filteredClosedTomitaDomainMap
          Stage sys ω hij x) := by
  change
    filteredGNSMap Stage sys ω hij
        (closedTomitaValue (ω.state i) x) =
      closedTomitaValue (ω.state j)
        (filteredClosedTomitaDomainMap
          Stage sys ω hij x)
  exact
    (closedTomitaValue_eq_of_mem
      (ω.state j) hclos_j
      (filteredClosedTomitaDomainMap
        Stage sys ω hij x)
      (filteredGNSMap Stage sys ω hij
        (closedTomitaValue (ω.state i) x))
      (filteredGNSMap_closedTomitaValue_mem_graph
        Stage sys ω hij x)).symm

end CStarStateColimit.Native.FilteredGNSTomitaClosedTransport

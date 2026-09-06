import InfoGeometry.Canonical.FilteredGNSTomitaClosability

/-!
# Closed conjugate-linear Tomita operator

Assuming the exact vertical-kernel closability criterion, the closed Tomita
relation is single-valued.  This file constructs its domain as a complex
submodule, derives the unique value from the closed graph, and bundles the
result as a conjugate-linear map.

Complex stability of the domain is not assumed.  It is proved by transporting
the algebraic graph and its closure under the twisted scalar action

`(ξ, η) ↦ (c • ξ, star c • η)`.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTomitaClosedOperator

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSTomitaCore
open CStarStateColimit.Native.FilteredGNSTomitaGraph
open CStarStateColimit.Native.FilteredGNSTomitaClosability
open Set

universe u

variable {A : Type u}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Twisted complex-scalar action appropriate to the graph of a
conjugate-linear operator. -/
def tomitaScalarPairMap
    (ω : State A) (c : ℂ) :
    ω.functional.GNS × ω.functional.GNS →
      ω.functional.GNS × ω.functional.GNS :=
  fun p => (c • p.1, star c • p.2)

theorem continuous_tomitaScalarPairMap
    (ω : State A) (c : ℂ) :
    Continuous (tomitaScalarPairMap ω c) :=
  (continuous_fst.const_smul c).prodMk
    (continuous_snd.const_smul (star c))

/-- The twisted scalar action preserves the algebraic Tomita graph. -/
theorem tomitaScalarPairMap_mapsTo_tomitaCoreGraph
    (ω : State A) (c : ℂ) :
    MapsTo (tomitaScalarPairMap ω c)
      (tomitaCoreGraph ω)
      (tomitaCoreGraph ω) := by
  rintro p ⟨x, rfl⟩
  refine ⟨c • x, ?_⟩
  ext
  · exact
      (UniformSpace.Completion.coe_smul c x).symm
  · rw [tomitaCore_smul]
    exact
      (UniformSpace.Completion.coe_smul
        (star c) (tomitaCore ω x)).symm

/-- The twisted scalar action preserves the closed Tomita relation. -/
theorem tomitaScalarPairMap_mapsTo_closedTomitaCoreGraph
    (ω : State A) (c : ℂ) :
    MapsTo (tomitaScalarPairMap ω c)
      (closedTomitaCoreGraph ω)
      (closedTomitaCoreGraph ω) := by
  exact
    (tomitaScalarPairMap_mapsTo_tomitaCoreGraph ω c).closure
      (continuous_tomitaScalarPairMap ω c)

/-- Domain projection of the closed Tomita relation.  Additivity follows from
the closed graph subgroup, while complex stability follows from the twisted
scalar graph action. -/
def closedTomitaDomain
    (ω : State A) :
    Submodule ℂ ω.functional.GNS where
  carrier :=
    {ξ | ∃ η, (ξ, η) ∈ closedTomitaCoreGraph ω}
  zero_mem' := by
    refine ⟨0, ?_⟩
    rw [← closedTomitaCoreGraphAddSubgroup_coe]
    exact (closedTomitaCoreGraphAddSubgroup ω).zero_mem
  add_mem' := by
    rintro x y ⟨η, hη⟩ ⟨ζ, hζ⟩
    refine ⟨η + ζ, ?_⟩
    rw [← closedTomitaCoreGraphAddSubgroup_coe] at hη hζ ⊢
    exact
      (closedTomitaCoreGraphAddSubgroup ω).add_mem hη hζ
  smul_mem' := by
    rintro c x ⟨η, hη⟩
    refine ⟨star c • η, ?_⟩
    exact
      tomitaScalarPairMap_mapsTo_closedTomitaCoreGraph
        ω c hη

/-- Chosen value of the closed relation on its domain.  Uniqueness is proved
below from closability. -/
noncomputable def closedTomitaValue
    (ω : State A)
    (x : closedTomitaDomain ω) :
    ω.functional.GNS :=
  Classical.choose x.property

theorem closedTomitaValue_mem_graph
    (ω : State A)
    (x : closedTomitaDomain ω) :
    (x.1, closedTomitaValue ω x) ∈
      closedTomitaCoreGraph ω :=
  Classical.choose_spec x.property

/-- Under closability, the chosen value equals every value related to the
same domain vector. -/
theorem closedTomitaValue_eq_of_mem
    (ω : State A)
    (hclos : IsClosableTomitaCore ω)
    (x : closedTomitaDomain ω)
    (η : ω.functional.GNS)
    (hη : (x.1, η) ∈ closedTomitaCoreGraph ω) :
    closedTomitaValue ω x = η := by
  exact
    (singleValued_closedTomitaCoreGraph_of_closable
      ω hclos)
      x.1 (closedTomitaValue ω x) η
      (closedTomitaValue_mem_graph ω x) hη

theorem closedTomitaValue_add
    (ω : State A)
    (hclos : IsClosableTomitaCore ω)
    (x y : closedTomitaDomain ω) :
    closedTomitaValue ω (x + y) =
    closedTomitaValue ω x +
        closedTomitaValue ω y := by
  apply closedTomitaValue_eq_of_mem ω hclos
  have hx :
      (x.1, closedTomitaValue ω x) ∈
        closedTomitaCoreGraphAddSubgroup ω := by
    show
      (x.1, closedTomitaValue ω x) ∈
        (closedTomitaCoreGraphAddSubgroup ω :
          Set (ω.functional.GNS × ω.functional.GNS))
    rw [closedTomitaCoreGraphAddSubgroup_coe]
    exact closedTomitaValue_mem_graph ω x
  have hy :
      (y.1, closedTomitaValue ω y) ∈
        closedTomitaCoreGraphAddSubgroup ω := by
    show
      (y.1, closedTomitaValue ω y) ∈
        (closedTomitaCoreGraphAddSubgroup ω :
          Set (ω.functional.GNS × ω.functional.GNS))
    rw [closedTomitaCoreGraphAddSubgroup_coe]
    exact closedTomitaValue_mem_graph ω y
  have hadd :=
    (closedTomitaCoreGraphAddSubgroup ω).add_mem hx hy
  show
    ((x + y : closedTomitaDomain ω).1,
        closedTomitaValue ω x +
          closedTomitaValue ω y) ∈
      closedTomitaCoreGraph ω
  rw [← closedTomitaCoreGraphAddSubgroup_coe]
  exact hadd

theorem closedTomitaValue_smul
    (ω : State A)
    (hclos : IsClosableTomitaCore ω)
    (c : ℂ)
    (x : closedTomitaDomain ω) :
    closedTomitaValue ω (c • x) =
      star c • closedTomitaValue ω x := by
  apply closedTomitaValue_eq_of_mem ω hclos
  exact
    tomitaScalarPairMap_mapsTo_closedTomitaCoreGraph
      ω c (closedTomitaValue_mem_graph ω x)

/-- Closed Tomita operator obtained from the single-valued closed relation. -/
noncomputable def closedTomitaOperator
    (ω : State A)
    (hclos : IsClosableTomitaCore ω) :
    closedTomitaDomain ω →ₛₗ[starRingEnd ℂ]
      ω.functional.GNS where
  toFun := closedTomitaValue ω
  map_add' := closedTomitaValue_add ω hclos
  map_smul' := closedTomitaValue_smul ω hclos

/-- Graph of the constructed closed conjugate-linear operator, viewed in the
ambient completed GNS product. -/
def closedTomitaOperatorGraph
    (ω : State A)
    (hclos : IsClosableTomitaCore ω) :
    Set (ω.functional.GNS × ω.functional.GNS) :=
  {p | ∃ x : closedTomitaDomain ω,
    p = (x.1, closedTomitaOperator ω hclos x)}

/-- The constructed operator has exactly the closed Tomita relation as its
graph. -/
theorem closedTomitaOperatorGraph_eq
    (ω : State A)
    (hclos : IsClosableTomitaCore ω) :
    closedTomitaOperatorGraph ω hclos =
      closedTomitaCoreGraph ω := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact closedTomitaValue_mem_graph ω x
  · intro hp
    let x : closedTomitaDomain ω :=
      ⟨p.1, ⟨p.2, hp⟩⟩
    refine ⟨x, ?_⟩
    apply Prod.ext
    · rfl
    · change
        p.2 =
          closedTomitaValue ω x
      exact
        (closedTomitaValue_eq_of_mem
          ω hclos x p.2 hp).symm

/-- Consequently, the graph of the constructed operator is closed. -/
theorem isClosed_closedTomitaOperatorGraph
    (ω : State A)
    (hclos : IsClosableTomitaCore ω) :
    IsClosed (closedTomitaOperatorGraph ω hclos) := by
  rw [closedTomitaOperatorGraph_eq]
  exact isClosed_closedTomitaCoreGraph ω

end CStarStateColimit.Native.FilteredGNSTomitaClosedOperator

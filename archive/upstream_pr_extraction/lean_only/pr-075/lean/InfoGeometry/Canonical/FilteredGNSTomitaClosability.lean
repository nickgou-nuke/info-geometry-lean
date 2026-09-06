import InfoGeometry.Canonical.FilteredGNSTomitaGraphClosure

/-!
# Closability criterion for filtered algebraic Tomita cores

The closure of an algebraic Tomita graph is initially only a closed relation.
This file proves that the graph and its closure are additive subgroups and
establishes the standard exact criterion:

`(0, η) ∈ closure (Graph S₀) → η = 0`

if and only if the closed relation is single-valued.  Thus no closed operator
is asserted until the vertical kernel of the closed relation is proved
trivial.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTomitaClosability

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSTomitaCore
open CStarStateColimit.Native.FilteredGNSTomitaGraph
open Set

universe u

variable {A : Type u}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The algebraic Tomita graph is an additive subgroup of the product of
completed GNS spaces.  Scalar closure is intentionally not claimed: the
Tomita core is conjugate-linear. -/
def tomitaCoreGraphAddSubgroup
    (ω : State A) :
    AddSubgroup (ω.functional.GNS × ω.functional.GNS) where
  carrier := tomitaCoreGraph ω
  zero_mem' := by
    refine ⟨0, ?_⟩
    ext
    · exact
        (UniformSpace.Completion.coe_zero
          (α := ω.functional.PreGNS)).symm
    · rw [tomitaCore_zero]
      exact
        (UniformSpace.Completion.coe_zero
          (α := ω.functional.PreGNS)).symm
  add_mem' := by
    rintro p q ⟨x, rfl⟩ ⟨y, rfl⟩
    refine ⟨x + y, ?_⟩
    ext
    · exact UniformSpace.Completion.coe_add x y |>.symm
    · rw [tomitaCore_add]
      exact
        UniformSpace.Completion.coe_add
          (tomitaCore ω x) (tomitaCore ω y) |>.symm
  neg_mem' := by
    rintro p ⟨x, rfl⟩
    refine ⟨-x, ?_⟩
    ext
    · exact UniformSpace.Completion.coe_neg x |>.symm
    · rw [tomitaCore_neg]
      exact
        UniformSpace.Completion.coe_neg
          (tomitaCore ω x) |>.symm

/-- Native topological additive-subgroup closure of the Tomita core graph. -/
def closedTomitaCoreGraphAddSubgroup
    (ω : State A) :
    AddSubgroup (ω.functional.GNS × ω.functional.GNS) :=
  (tomitaCoreGraphAddSubgroup ω).topologicalClosure

/-- The bundled subgroup closure has exactly the previously defined closed
Tomita relation as its carrier. -/
theorem closedTomitaCoreGraphAddSubgroup_coe
    (ω : State A) :
    (closedTomitaCoreGraphAddSubgroup ω :
      Set (ω.functional.GNS × ω.functional.GNS)) =
      closedTomitaCoreGraph ω := by
  exact AddSubgroup.topologicalClosure_coe

/-- The closed Tomita relation has trivial vertical kernel.  This is the
operator-theoretic closability criterion, stated without pretending that the
closed relation is already a function. -/
def IsClosableTomitaCore
    (ω : State A) : Prop :=
  ∀ η : ω.functional.GNS,
    (0, η) ∈ closedTomitaCoreGraph ω →
      η = 0

/-- A binary relation represented as a subset of a product is
single-valued. -/
def IsSingleValuedRelation
    {X Y : Type*}
    (R : Set (X × Y)) : Prop :=
  ∀ x y z, (x, y) ∈ R → (x, z) ∈ R → y = z

/-- Triviality of the vertical kernel forces the closed additive Tomita
relation to be single-valued. -/
theorem singleValued_closedTomitaCoreGraph_of_closable
    (ω : State A)
    (hclos : IsClosableTomitaCore ω) :
    IsSingleValuedRelation
      (closedTomitaCoreGraph ω) := by
  intro x y z hxy hxz
  let G := closedTomitaCoreGraphAddSubgroup ω
  have hxy' : (x, y) ∈ G := by
    show
      (x, y) ∈
        (closedTomitaCoreGraphAddSubgroup ω :
          Set (ω.functional.GNS × ω.functional.GNS))
    rw [closedTomitaCoreGraphAddSubgroup_coe]
    exact hxy
  have hxz' : (x, z) ∈ G := by
    show
      (x, z) ∈
        (closedTomitaCoreGraphAddSubgroup ω :
          Set (ω.functional.GNS × ω.functional.GNS))
    rw [closedTomitaCoreGraphAddSubgroup_coe]
    exact hxz
  have hsub : (x, y) - (x, z) ∈ G :=
    G.sub_mem hxy' hxz'
  have hvert : (0, y - z) ∈
      closedTomitaCoreGraph ω := by
    rw [← closedTomitaCoreGraphAddSubgroup_coe]
    simpa using hsub
  exact sub_eq_zero.mp (hclos (y - z) hvert)

/-- Conversely, a single-valued closed Tomita relation has trivial vertical
kernel because it already contains `(0,0)`. -/
theorem closable_of_singleValued_closedTomitaCoreGraph
    (ω : State A)
    (hsv :
      IsSingleValuedRelation
        (closedTomitaCoreGraph ω)) :
    IsClosableTomitaCore ω := by
  intro η hη
  have hzero :
      (0, (0 : ω.functional.GNS)) ∈
        closedTomitaCoreGraph ω := by
    rw [← closedTomitaCoreGraphAddSubgroup_coe]
    exact (closedTomitaCoreGraphAddSubgroup ω).zero_mem
  exact hsv 0 η 0 hη hzero

/-- Exact graph-theoretic characterization of Tomita-core closability. -/
theorem closable_iff_singleValued_closedTomitaCoreGraph
    (ω : State A) :
    IsClosableTomitaCore ω ↔
      IsSingleValuedRelation
        (closedTomitaCoreGraph ω) :=
  ⟨singleValued_closedTomitaCoreGraph_of_closable ω,
    closable_of_singleValued_closedTomitaCoreGraph ω⟩

end CStarStateColimit.Native.FilteredGNSTomitaClosability

import InfoGeometry.Canonical.FilteredGNSTomitaCore
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Topological closure of filtered algebraic Tomita graphs

The algebraic Tomita operation need not be bounded on the completed GNS space.
Its correct first topological carrier is therefore its graph inside the product
of two completed GNS spaces.  This file proves that genuine star-homomorphic
GNS transport maps algebraic Tomita graphs into one another and, by
continuity, maps their closures into one another.

The closed set defined here is the closure of the algebraic graph.  We do not
claim that it is the graph of a single-valued closed operator; that additional
statement is precisely the closability frontier.
-/

noncomputable section

namespace CStarStateColimit.Native.FilteredGNSTomitaGraph

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNS
open CStarStateColimit.Native.FilteredGNSTomitaCore
open Set

universe u

variable {A B : Type u}
variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Graph of the algebraic Tomita operation inside the product of completed
GNS spaces. -/
def tomitaCoreGraph
    (ω : State A) :
    Set (ω.functional.GNS × ω.functional.GNS) :=
  {p | ∃ x : ω.functional.PreGNS,
    p =
      ((x : ω.functional.GNS),
        (tomitaCore ω x : ω.functional.GNS))}

/-- Topological closure of the algebraic Tomita graph. -/
def closedTomitaCoreGraph
    (ω : State A) :
    Set (ω.functional.GNS × ω.functional.GNS) :=
  closure (tomitaCoreGraph ω)

theorem isClosed_closedTomitaCoreGraph
    (ω : State A) :
    IsClosed (closedTomitaCoreGraph ω) :=
  isClosed_closure

/-- Product map induced by completed GNS transport. -/
def gnsPairMap
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B) :
    (ω.restrict f).functional.GNS ×
        (ω.restrict f).functional.GNS →
      ω.functional.GNS × ω.functional.GNS :=
  fun p => (gnsMap f ω p.1, gnsMap f ω p.2)

theorem continuous_gnsPairMap
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B) :
    Continuous (gnsPairMap f ω) :=
  ((gnsMap_isometry f ω).continuous.comp continuous_fst).prodMk
    ((gnsMap_isometry f ω).continuous.comp continuous_snd)

/-- Completed GNS transport agrees with pre-GNS transport on every algebraic
vector. -/
theorem gnsMap_coe_preGNSMap
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B)
    (x : (ω.restrict f).functional.PreGNS) :
    gnsMap f ω
        (x : (ω.restrict f).functional.GNS) =
      (preGNSMap f ω x : ω.functional.GNS) := by
  obtain ⟨a, rfl⟩ :=
    (ω.restrict f).functional.toPreGNS.surjective x
  simp

/-- A genuine star-homomorphism maps the source algebraic Tomita graph into
the target algebraic Tomita graph. -/
theorem gnsPairMap_mapsTo_tomitaCoreGraph
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B) :
    MapsTo (gnsPairMap f ω)
      (tomitaCoreGraph (ω.restrict f))
      (tomitaCoreGraph ω) := by
  rintro p ⟨x, rfl⟩
  refine ⟨preGNSMap f ω x, ?_⟩
  ext
  · exact gnsMap_coe_preGNSMap f ω x
  · change
      gnsMap f ω
          ((tomitaCore (ω.restrict f) x :
            (ω.restrict f).functional.PreGNS) :
            (ω.restrict f).functional.GNS) =
        ((tomitaCore ω (preGNSMap f ω x) :
          ω.functional.PreGNS) :
          ω.functional.GNS)
    rw [gnsMap_coe_preGNSMap]
    exact congrArg
      (fun y : ω.functional.PreGNS =>
        (y : ω.functional.GNS))
      (preGNSMap_tomitaCore f ω x)

/-- Continuity upgrades algebraic graph transport to transport of the
topological graph closures. -/
theorem gnsPairMap_mapsTo_closedTomitaCoreGraph
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B) :
    MapsTo (gnsPairMap f ω)
      (closedTomitaCoreGraph (ω.restrict f))
      (closedTomitaCoreGraph ω) := by
  exact
    (gnsPairMap_mapsTo_tomitaCoreGraph f ω).closure
      (continuous_gnsPairMap f ω)

section Filtered

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

/-- Product of a filtered completed-GNS transition with itself. -/
def filteredGNSPairMap
    {i j : I} (hij : i ≤ j) :
    (ω.state i).functional.GNS ×
        (ω.state i).functional.GNS →
      (ω.state j).functional.GNS ×
        (ω.state j).functional.GNS :=
  fun p =>
    (filteredGNSMap Stage sys ω hij p.1,
      filteredGNSMap Stage sys ω hij p.2)

theorem continuous_filteredGNSPairMap
    {i j : I} (hij : i ≤ j) :
    Continuous (filteredGNSPairMap Stage sys ω hij) :=
  ((filteredGNSMap_isometry Stage sys ω hij).continuous.comp
      continuous_fst).prodMk
    ((filteredGNSMap_isometry Stage sys ω hij).continuous.comp
      continuous_snd)

/-- Filtered transitions preserve the algebraic Tomita graphs. -/
theorem filteredGNSPairMap_mapsTo_tomitaCoreGraph
    {i j : I} (hij : i ≤ j) :
    MapsTo (filteredGNSPairMap Stage sys ω hij)
      (tomitaCoreGraph (ω.state i))
      (tomitaCoreGraph (ω.state j)) := by
  rintro p ⟨x, rfl⟩
  obtain ⟨a, rfl⟩ :=
    (ω.state i).functional.toPreGNS.surjective x
  refine
    ⟨(ω.state j).functional.toPreGNS
      (sys.map hij a), ?_⟩
  ext
  · simp [filteredGNSPairMap]
  · change
      filteredGNSMap Stage sys ω hij
          ((tomitaCore (ω.state i)
            ((ω.state i).functional.toPreGNS a) :
              (ω.state i).functional.PreGNS) :
            (ω.state i).functional.GNS) =
        ((tomitaCore (ω.state j)
            ((ω.state j).functional.toPreGNS
              (sys.map hij a)) :
              (ω.state j).functional.PreGNS) :
          (ω.state j).functional.GNS)
    exact
      filteredGNSMap_tomitaCore_toPreGNS
        Stage sys ω hij a

/-- Filtered transitions preserve the closures of the algebraic Tomita
graphs. -/
theorem filteredGNSPairMap_mapsTo_closedTomitaCoreGraph
    {i j : I} (hij : i ≤ j) :
    MapsTo (filteredGNSPairMap Stage sys ω hij)
      (closedTomitaCoreGraph (ω.state i))
      (closedTomitaCoreGraph (ω.state j)) := by
  exact
    (filteredGNSPairMap_mapsTo_tomitaCoreGraph
      Stage sys ω hij).closure
      (continuous_filteredGNSPairMap Stage sys ω hij)

end Filtered

end CStarStateColimit.Native.FilteredGNSTomitaGraph

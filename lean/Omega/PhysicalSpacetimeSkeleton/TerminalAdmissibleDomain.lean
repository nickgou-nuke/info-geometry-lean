import Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure

namespace Omega.PhysicalSpacetimeSkeleton

universe u

open Omega.PhysicalSpacetimeSkeleton.GlobalLorentzStructure

/-- Concrete data for a terminal admissible domain attached to a finite compatible Lorentz family. -/
structure TerminalAdmissibleDomainData where
  ι : Type u
  instFintype : Fintype ι
  family : CompatibleLorentzFamily ι

attribute [instance] TerminalAdmissibleDomainData.instFintype

namespace TerminalAdmissibleDomainData

abbrev chartPoint (D : TerminalAdmissibleDomainData) := ChartPoint D.family

abbrev terminalDomain (D : TerminalAdmissibleDomainData) :=
  maximalAdmissibleDomain D.family

/-- A finite glued atlas is a quotient of the disjoint chart union. -/
structure AdmissibleAtlas (D : TerminalAdmissibleDomainData) where
  rel : Setoid D.chartPoint

namespace AdmissibleAtlas

abbrev domain {D : TerminalAdmissibleDomainData} (A : AdmissibleAtlas D) :=
  Quotient A.rel

def point {D : TerminalAdmissibleDomainData} (A : AdmissibleAtlas D)
    (i : D.ι) (x : D.family.Chart i) : A.domain :=
  Quotient.mk A.rel ⟨i, x⟩

def canonicalMap {D : TerminalAdmissibleDomainData} (A : AdmissibleAtlas D)
    (rel_sub_overlap : ∀ {p q : D.chartPoint}, A.rel.r p q →
      (chartPointSetoid D.family).r p q) :
    A.domain → D.terminalDomain :=
  Quotient.lift
    (fun p : D.chartPoint => Quotient.mk (chartPointSetoid D.family) p)
    (fun _ _ h => Quotient.sound (rel_sub_overlap h))

lemma canonicalMap_point {D : TerminalAdmissibleDomainData} (A : AdmissibleAtlas D)
    (rel_sub_overlap : ∀ {p q : D.chartPoint}, A.rel.r p q →
      (chartPointSetoid D.family).r p q)
    (i : D.ι) (x : D.family.Chart i) :
    A.canonicalMap rel_sub_overlap (A.point i x) = pointClass D.family i x := by
  rfl

end AdmissibleAtlas

lemma unique_map_to_terminalDomain (D : TerminalAdmissibleDomainData)
    (A : AdmissibleAtlas D)
    (rel_sub_overlap : ∀ {p q : D.chartPoint}, A.rel.r p q →
      (chartPointSetoid D.family).r p q) :
    ∃! f : A.domain → D.terminalDomain, ∀ i x,
      f (A.point i x) = pointClass D.family i x := by
  refine ⟨A.canonicalMap rel_sub_overlap, A.canonicalMap_point rel_sub_overlap, ?_⟩
  intro f hf
  funext q
  refine Quotient.inductionOn q ?_
  intro p
  rcases p with ⟨i, x⟩
  simpa [AdmissibleAtlas.point] using hf i x

end TerminalAdmissibleDomainData

open TerminalAdmissibleDomainData

/-- The maximal quotient has the unique descended metric and receives a unique comparison map
from every compatible finite glued atlas. -/
theorem paper_physical_spacetime_terminal_admissible_domain
    (D : TerminalAdmissibleDomainData)
    (metric_compat :
      ∀ {i j} {x : D.family.Chart i} {y : D.family.Chart j},
        D.family.overlapSetoid.r ⟨i, x⟩ ⟨j, y⟩ →
          D.family.metric i x = D.family.metric j y) :
    (∃! g : D.terminalDomain → ℝ,
      ∀ i x, g (pointClass D.family i x) = D.family.metric i x) ∧
      ∀ (A : AdmissibleAtlas D),
        (∀ {p q : D.chartPoint}, A.rel.r p q → (chartPointSetoid D.family).r p q) →
          ∃! f : A.domain → D.terminalDomain, ∀ i x,
            f (A.point i x) = pointClass D.family i x := by
  refine ⟨?_, ?_⟩
  · simpa [TerminalAdmissibleDomainData.terminalDomain] using
      (paper_physical_spacetime_finite_compatible_family_glues D.family metric_compat)
  · intro A hA
    exact D.unique_map_to_terminalDomain A hA

end Omega.PhysicalSpacetimeSkeleton

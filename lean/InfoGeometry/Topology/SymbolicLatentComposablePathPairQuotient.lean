import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathConcatenationHomotopy
import InfoGeometry.Topology.SymbolicLatentPathConcatenationNaturality
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotient
import InfoGeometry.Topology.SymbolicLatentPathHomotopyQuotientFunctoriality

namespace InfoGeometry.Topology

/-!
# Quotient of composable symbolic-latent path pairs

The ordinary product of path-homotopy quotients does not remember a proof that
the two endpoint values match.  This owner keeps that proof in the source
object and then quotients componentwise.  The midpoint-glued concatenation
therefore descends without choosing an artificial value for non-composable
pairs.
-/

abbrev SymbolicLatentComposablePathPair
    {X : Type*} [TopologicalSpace X] :=
  {p : SymbolicLatentPath X × SymbolicLatentPath X //
    p.1.finish = p.2.start}

namespace SymbolicLatentComposablePathPair

abbrev first
    {X : Type*} [TopologicalSpace X]
    (p : SymbolicLatentComposablePathPair (X := X)) : SymbolicLatentPath X := p.1.1

abbrev second
    {X : Type*} [TopologicalSpace X]
    (p : SymbolicLatentComposablePathPair (X := X)) : SymbolicLatentPath X := p.1.2

abbrev composable
    {X : Type*} [TopologicalSpace X]
    (p : SymbolicLatentComposablePathPair (X := X)) :
    p.first.finish = p.second.start := p.2

end SymbolicLatentComposablePathPair

def symbolicLatentComposablePathPairSetoid
    {X : Type*} [TopologicalSpace X] :
    Setoid (SymbolicLatentComposablePathPair (X := X)) where
  r p q :=
    SymbolicLatentPathHomotopic p.first q.first ∧
      SymbolicLatentPathHomotopic p.second q.second
  iseqv := by
    constructor
    · intro p
      exact ⟨SymbolicLatentPathHomotopic.refl p.first,
        SymbolicLatentPathHomotopic.refl p.second⟩
    · intro p q h
      exact ⟨h.1.symm, h.2.symm⟩
    · intro p q r hpq hqr
      exact ⟨hpq.1.trans hqr.1, hpq.2.trans hqr.2⟩

abbrev SymbolicLatentComposablePathPairQuotient
    {X : Type*} [TopologicalSpace X] :=
  Quotient (symbolicLatentComposablePathPairSetoid (X := X))

def symbolicLatentComposablePathPairQuotientMap
    {X : Type*} [TopologicalSpace X] :
    SymbolicLatentComposablePathPair (X := X) →
      SymbolicLatentComposablePathPairQuotient (X := X) :=
  Quotient.mk' (s := symbolicLatentComposablePathPairSetoid (X := X))

noncomputable def symbolicLatentComposablePathPairConcatenationQuotientMap
    {X : Type*} [TopologicalSpace X] :
    SymbolicLatentComposablePathPairQuotient (X := X) →
      SymbolicLatentPathHomotopyQuotient (X := X) :=
  Quotient.lift
    (fun p => symbolicLatentPathHomotopyQuotientMap
      (canonicalSymbolicConcatenation p.composable))
    (by
      intro p q hpq
      apply Quotient.sound
      rcases hpq.1 with ⟨H₀⟩
      rcases hpq.2 with ⟨H₁⟩
      exact concatenatedSymbolicPathHomotopic_of_homotopies
        p.composable q.composable H₀ H₁)

theorem symbolicLatentComposablePathPairConcatenationQuotientMap_mk
    {X : Type*} [TopologicalSpace X]
    (p : SymbolicLatentComposablePathPair (X := X)) :
    symbolicLatentComposablePathPairConcatenationQuotientMap
        (symbolicLatentComposablePathPairQuotientMap p) =
      symbolicLatentPathHomotopyQuotientMap
        (canonicalSymbolicConcatenation p.composable) :=
  rfl

theorem symbolicLatentComposablePathPairConcatenationQuotientMap_well_defined
    {X : Type*} [TopologicalSpace X]
    {p q : SymbolicLatentComposablePathPair (X := X)}
    (h : (symbolicLatentComposablePathPairSetoid (X := X)).r p q) :
    symbolicLatentPathHomotopyQuotientMap
        (canonicalSymbolicConcatenation p.composable) =
      symbolicLatentPathHomotopyQuotientMap
        (canonicalSymbolicConcatenation q.composable) := by
  apply Quotient.sound
  rcases h.1 with ⟨H₀⟩
  rcases h.2 with ⟨H₁⟩
  exact concatenatedSymbolicPathHomotopic_of_homotopies
    p.composable q.composable H₀ H₁

theorem symbolicLatentComposablePathPairConcatenationQuotientMap_endpoint
    {X : Type*} [TopologicalSpace X]
    (p : SymbolicLatentComposablePathPair (X := X)) :
    symbolicLatentPathHomotopyEndpointMap
        (symbolicLatentComposablePathPairConcatenationQuotientMap
          (symbolicLatentComposablePathPairQuotientMap p)) =
      (p.first.start, p.second.finish) := by
  rw [symbolicLatentComposablePathPairConcatenationQuotientMap_mk,
    symbolicLatentPathHomotopyEndpointMap_mk]
  apply Prod.ext
  · exact (canonicalSymbolicLatentPathConcatenation p.composable).start_eq_first_start
  · exact (canonicalSymbolicLatentPathConcatenation p.composable).finish_eq_second_finish

noncomputable def mapSymbolicLatentComposablePathPair
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y))
    (p : SymbolicLatentComposablePathPair (X := X)) :
    SymbolicLatentComposablePathPair (X := Y) :=
  ⟨⟨mapSymbolicLatentPathContinuous f f.continuous p.first,
      mapSymbolicLatentPathContinuous f f.continuous p.second⟩,
    congrArg f p.composable⟩

noncomputable def mapSymbolicLatentComposablePathPairQuotient
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    SymbolicLatentComposablePathPairQuotient (X := X) →
      SymbolicLatentComposablePathPairQuotient (X := Y) :=
  Quotient.lift
    (fun p => symbolicLatentComposablePathPairQuotientMap
      (mapSymbolicLatentComposablePathPair f p))
    (by
      intro p q hpq
      apply Quotient.sound
      exact ⟨mapSymbolicLatentPathHomotopic f hpq.1,
        mapSymbolicLatentPathHomotopic f hpq.2⟩)

theorem mapSymbolicLatentComposablePathPairQuotient_mk
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y))
    (p : SymbolicLatentComposablePathPair (X := X)) :
    mapSymbolicLatentComposablePathPairQuotient f
        (symbolicLatentComposablePathPairQuotientMap p) =
      symbolicLatentComposablePathPairQuotientMap
        (mapSymbolicLatentComposablePathPair f p) :=
  rfl

theorem mapSymbolicLatentComposablePathPairQuotient_concatenation_natural
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y))
    (q : SymbolicLatentComposablePathPairQuotient (X := X)) :
    symbolicLatentComposablePathPairConcatenationQuotientMap
        (mapSymbolicLatentComposablePathPairQuotient f q) =
      mapSymbolicLatentPathHomotopyQuotient f
        (symbolicLatentComposablePathPairConcatenationQuotientMap q) := by
  refine Quotient.inductionOn q ?_
  intro p
  apply Quotient.sound
  rcases mapSymbolicLatentPathContinuous_canonicalSymbolicConcatenation_of_map
    f f.continuous p.composable with ⟨hend_map, hpath⟩
  have hconcat_eq :
      canonicalSymbolicConcatenation
          (mapSymbolicLatentComposablePathPair f p).composable =
        f.comp (canonicalSymbolicConcatenation p.composable) := by
    calc
      canonicalSymbolicConcatenation
          (mapSymbolicLatentComposablePathPair f p).composable =
          canonicalSymbolicConcatenation hend_map := by
            congr 1
      _ = mapSymbolicLatentPathContinuous f f.continuous
          (canonicalSymbolicConcatenation p.composable) := hpath.symm
      _ = f.comp (canonicalSymbolicConcatenation p.composable) := by
        rfl
  rw [hconcat_eq]
  exact SymbolicLatentPathHomotopic.refl _


end InfoGeometry.Topology

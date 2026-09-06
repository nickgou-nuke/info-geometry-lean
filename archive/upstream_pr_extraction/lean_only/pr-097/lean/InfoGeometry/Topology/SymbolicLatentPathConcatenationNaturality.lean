import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathConcatenationConstruction
import InfoGeometry.Topology.SymbolicLatentPathFunctoriality

namespace InfoGeometry.Topology

/-!
# Naturality of the canonical concatenation

The explicit midpoint gluing is functorial for continuous maps.  This is the
missing bridge from the concrete path constructor to chart, observation, and
quotient transport owners.
-/

theorem mapSymbolicLatentPathContinuous_canonicalSymbolicConcatenation
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (f : X → Y) (hf : Continuous f)
    (hend : γ₀.finish = γ₁.start)
    (hend_map :
      (mapSymbolicLatentPathContinuous f hf γ₀).finish =
        (mapSymbolicLatentPathContinuous f hf γ₁).start) :
    mapSymbolicLatentPathContinuous f hf
        (canonicalSymbolicConcatenation hend) =
      canonicalSymbolicConcatenation hend_map := by
  ext t
  by_cases ht : t ∈ Set.Iic symbolicConcatenationMidpoint
  · have hp := Set.piecewise_eq_of_mem
      (s := Set.Iic symbolicConcatenationMidpoint)
      (f := (γ₀.comp symbolicConcatenationFirstParameter))
      (g := (γ₁.comp symbolicConcatenationSecondParameter)) ht
    have hp' := Set.piecewise_eq_of_mem
      (s := Set.Iic symbolicConcatenationMidpoint)
      (f := ((mapSymbolicLatentPathContinuous f hf γ₀).comp
        symbolicConcatenationFirstParameter))
      (g := ((mapSymbolicLatentPathContinuous f hf γ₁).comp
        symbolicConcatenationSecondParameter)) ht
    change f ((Set.Iic symbolicConcatenationMidpoint).piecewise
        (γ₀.comp symbolicConcatenationFirstParameter)
        (γ₁.comp symbolicConcatenationSecondParameter) t) =
      (Set.Iic symbolicConcatenationMidpoint).piecewise
        ((mapSymbolicLatentPathContinuous f hf γ₀).comp
          symbolicConcatenationFirstParameter)
        ((mapSymbolicLatentPathContinuous f hf γ₁).comp
          symbolicConcatenationSecondParameter) t
    rw [hp, hp']
    rfl
  · have hp := Set.piecewise_eq_of_notMem
      (s := Set.Iic symbolicConcatenationMidpoint)
      (f := (γ₀.comp symbolicConcatenationFirstParameter))
      (g := (γ₁.comp symbolicConcatenationSecondParameter)) ht
    have hp' := Set.piecewise_eq_of_notMem
      (s := Set.Iic symbolicConcatenationMidpoint)
      (f := ((mapSymbolicLatentPathContinuous f hf γ₀).comp
        symbolicConcatenationFirstParameter))
      (g := ((mapSymbolicLatentPathContinuous f hf γ₁).comp
        symbolicConcatenationSecondParameter)) ht
    change f ((Set.Iic symbolicConcatenationMidpoint).piecewise
        (γ₀.comp symbolicConcatenationFirstParameter)
        (γ₁.comp symbolicConcatenationSecondParameter) t) =
      (Set.Iic symbolicConcatenationMidpoint).piecewise
        ((mapSymbolicLatentPathContinuous f hf γ₀).comp
          symbolicConcatenationFirstParameter)
        ((mapSymbolicLatentPathContinuous f hf γ₁).comp
          symbolicConcatenationSecondParameter) t
    rw [hp, hp']
    rfl

theorem mapSymbolicLatentPathContinuous_canonicalSymbolicConcatenation_of_map
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (f : X → Y) (hf : Continuous f)
    (hend : γ₀.finish = γ₁.start) :
    ∃ hend_map :
      (mapSymbolicLatentPathContinuous f hf γ₀).finish =
        (mapSymbolicLatentPathContinuous f hf γ₁).start,
      mapSymbolicLatentPathContinuous f hf
          (canonicalSymbolicConcatenation hend) =
        canonicalSymbolicConcatenation hend_map := by
  let hend_map :
      (mapSymbolicLatentPathContinuous f hf γ₀).finish =
        (mapSymbolicLatentPathContinuous f hf γ₁).start := by
    change f γ₀.finish = f γ₁.start
    exact congrArg f hend
  exact ⟨hend_map,
    mapSymbolicLatentPathContinuous_canonicalSymbolicConcatenation
      f hf hend hend_map⟩

theorem mapSymbolicLatentPathContinuous_canonicalSymbolicConcatenation_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (f : X → Y) (g : Y → Z)
    (hf : Continuous f) (hg : Continuous g)
    (hend : γ₀.finish = γ₁.start) :
    ∃ hend_map :
      (mapSymbolicLatentPathContinuous (g ∘ f) (hg.comp hf) γ₀).finish =
        (mapSymbolicLatentPathContinuous (g ∘ f) (hg.comp hf) γ₁).start,
      mapSymbolicLatentPathContinuous (g ∘ f) (hg.comp hf)
          (canonicalSymbolicConcatenation hend) =
        canonicalSymbolicConcatenation hend_map := by
  let hend_f :
      (mapSymbolicLatentPathContinuous f hf γ₀).finish =
        (mapSymbolicLatentPathContinuous f hf γ₁).start := by
    change f γ₀.finish = f γ₁.start
    exact congrArg f hend
  let hend_g :
      (mapSymbolicLatentPathContinuous (g ∘ f) (hg.comp hf) γ₀).finish =
        (mapSymbolicLatentPathContinuous (g ∘ f) (hg.comp hf) γ₁).start := by
    change g (f γ₀.finish) = g (f γ₁.start)
    exact congrArg g hend_f
  refine ⟨hend_g, ?_⟩
  calc
    mapSymbolicLatentPathContinuous (g ∘ f) (hg.comp hf)
        (canonicalSymbolicConcatenation hend)
      = mapSymbolicLatentPathContinuous g hg
          (mapSymbolicLatentPathContinuous f hf
            (canonicalSymbolicConcatenation hend)) := by
          symm
          exact mapSymbolicLatentPathContinuous_comp f g hf hg
            (canonicalSymbolicConcatenation hend)
    _ = mapSymbolicLatentPathContinuous g hg
          (canonicalSymbolicConcatenation hend_f) := by
          rw [mapSymbolicLatentPathContinuous_canonicalSymbolicConcatenation
            (f := f) (hf := hf) hend hend_f]
    _ = canonicalSymbolicConcatenation hend_g := by
          exact mapSymbolicLatentPathContinuous_canonicalSymbolicConcatenation
            (f := g) (hf := hg) hend_f hend_g

end InfoGeometry.Topology

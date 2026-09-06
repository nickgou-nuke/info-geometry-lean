import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathConcatenationConstruction

namespace InfoGeometry.Topology

/-!
# Image coverage for canonical symbolic-latent concatenation

The piecewise construction does not add points to the path image: its image
is exactly the union of the two input images.  This is the topological support
invariant needed when transporting compactness or feasible-set membership
through a concatenation.
-/

theorem canonicalSymbolicConcatenation_range_eq_union
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) :
    Set.range (canonicalSymbolicConcatenation hend) =
      Set.range γ₀ ∪ Set.range γ₁ := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    by_cases ht : t ∈ Set.Iic symbolicConcatenationMidpoint
    · left
      refine ⟨symbolicConcatenationFirstParameter t, ?_⟩
      change γ₀ (symbolicConcatenationFirstParameter t) =
        Set.piecewise (Set.Iic symbolicConcatenationMidpoint)
          (γ₀.comp symbolicConcatenationFirstParameter)
          (γ₁.comp symbolicConcatenationSecondParameter) t
      have hp := Set.piecewise_eq_of_mem
        (s := Set.Iic symbolicConcatenationMidpoint)
        (f := (γ₀.comp symbolicConcatenationFirstParameter))
        (g := (γ₁.comp symbolicConcatenationSecondParameter)) ht
      rw [hp]
      rfl
    · right
      refine ⟨symbolicConcatenationSecondParameter t, ?_⟩
      change γ₁ (symbolicConcatenationSecondParameter t) =
        Set.piecewise (Set.Iic symbolicConcatenationMidpoint)
          (γ₀.comp symbolicConcatenationFirstParameter)
          (γ₁.comp symbolicConcatenationSecondParameter) t
      have hp := Set.piecewise_eq_of_notMem
        (s := Set.Iic symbolicConcatenationMidpoint)
        (f := (γ₀.comp symbolicConcatenationFirstParameter))
        (g := (γ₁.comp symbolicConcatenationSecondParameter)) ht
      rw [hp]
      rfl
  · intro hx
    rcases hx with hx | hx
    · rcases hx with ⟨t, rfl⟩
      refine ⟨symbolicFirstHalfParameter t, ?_⟩
      exact canonicalSymbolicConcatenation_first_half hend t
    · rcases hx with ⟨t, rfl⟩
      refine ⟨symbolicSecondHalfParameter t, ?_⟩
      exact canonicalSymbolicConcatenation_second_half hend t

theorem canonicalSymbolicConcatenation_image_subset_union
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) :
    Set.range (canonicalSymbolicConcatenation hend) ⊆
      Set.range γ₀ ∪ Set.range γ₁ := by
  rw [canonicalSymbolicConcatenation_range_eq_union hend]

end InfoGeometry.Topology

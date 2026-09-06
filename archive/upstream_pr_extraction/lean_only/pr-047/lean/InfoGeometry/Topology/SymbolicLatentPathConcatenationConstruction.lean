import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathConcatenation

namespace InfoGeometry.Topology

/-!
# Canonical continuous concatenation of symbolic-latent paths

The path is glued at the midpoint.  Endpoint compatibility is the only
matching condition; continuity is proved by the native piecewise gluing
theorem on the interval subtype.
-/

noncomputable def symbolicConcatenationMidpoint : SymbolicPathDomain :=
  ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

noncomputable def symbolicConcatenationFirstParameter :
    C(SymbolicPathDomain, SymbolicPathDomain) :=
  ⟨fun t => ⟨min (2 * (t : ℝ)) 1, by
      constructor
      · apply le_min
        · exact mul_nonneg (by norm_num) t.property.1
        · norm_num
      · exact min_le_right _ _⟩,
    by
      continuity⟩

noncomputable def symbolicConcatenationSecondParameter :
    C(SymbolicPathDomain, SymbolicPathDomain) :=
  ⟨fun t => ⟨max (2 * (t : ℝ) - 1) 0, by
      constructor
      · exact le_trans (by norm_num) (le_max_right _ _)
      · apply max_le
        · linarith [t.property.2]
        · norm_num⟩,
    by
      continuity⟩

noncomputable def symbolicConcatenationFunction
    {X : Type*} [TopologicalSpace X]
    (γ₀ γ₁ : SymbolicLatentPath X) : SymbolicPathDomain → X :=
  Set.piecewise (Set.Iic symbolicConcatenationMidpoint)
    (γ₀.comp symbolicConcatenationFirstParameter)
    (γ₁.comp symbolicConcatenationSecondParameter)

theorem symbolicConcatenationFunction_continuous
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) :
    Continuous (symbolicConcatenationFunction γ₀ γ₁) := by
  apply continuous_piecewise
  · intro t ht
    have ht' : t = symbolicConcatenationMidpoint := by
      exact Set.mem_singleton_iff.mp (frontier_Iic_subset
        symbolicConcatenationMidpoint ht)
    subst t
    change (γ₀.comp symbolicConcatenationFirstParameter)
        symbolicConcatenationMidpoint =
      (γ₁.comp symbolicConcatenationSecondParameter)
        symbolicConcatenationMidpoint
    change γ₀ (symbolicConcatenationFirstParameter symbolicConcatenationMidpoint) =
      γ₁ (symbolicConcatenationSecondParameter symbolicConcatenationMidpoint)
    have hfirst : symbolicConcatenationFirstParameter symbolicConcatenationMidpoint =
        (1 : SymbolicPathDomain) := by
      apply Subtype.ext
      norm_num [symbolicConcatenationFirstParameter, symbolicConcatenationMidpoint]
    have hsecond : symbolicConcatenationSecondParameter symbolicConcatenationMidpoint =
        (0 : SymbolicPathDomain) := by
      apply Subtype.ext
      norm_num [symbolicConcatenationSecondParameter, symbolicConcatenationMidpoint]
    rw [hfirst, hsecond]
    exact hend
  · exact (γ₀.comp symbolicConcatenationFirstParameter).continuous.continuousOn
  · exact (γ₁.comp symbolicConcatenationSecondParameter).continuous.continuousOn

noncomputable def canonicalSymbolicConcatenation
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) : SymbolicLatentPath X :=
  { toFun := symbolicConcatenationFunction γ₀ γ₁
    continuous_toFun := symbolicConcatenationFunction_continuous hend }

theorem canonicalSymbolicConcatenation_first_half
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) (t : SymbolicPathDomain) :
    canonicalSymbolicConcatenation hend
      (symbolicFirstHalfParameter t) = γ₀ t := by
  change Set.piecewise (Set.Iic symbolicConcatenationMidpoint)
      (γ₀.comp symbolicConcatenationFirstParameter)
      (γ₁.comp symbolicConcatenationSecondParameter)
      (symbolicFirstHalfParameter t) = γ₀ t
  rw [Set.piecewise_eq_of_mem]
  · change γ₀ (symbolicConcatenationFirstParameter
      (symbolicFirstHalfParameter t)) = γ₀ t
    congr 1
    apply Subtype.ext
    change min (2 * ((t : ℝ) / 2)) 1 = (t : ℝ)
    rw [min_eq_left]
    · ring
    · linarith [t.property.2]
  · change (symbolicFirstHalfParameter t : ℝ) ≤
      (symbolicConcatenationMidpoint : ℝ)
    change (t : ℝ) / 2 ≤ 1 / 2
    linarith [t.property.2]

theorem canonicalSymbolicConcatenation_second_half
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) (t : SymbolicPathDomain) :
    canonicalSymbolicConcatenation hend
      (symbolicSecondHalfParameter t) = γ₁ t := by
  change Set.piecewise (Set.Iic symbolicConcatenationMidpoint)
      (γ₀.comp symbolicConcatenationFirstParameter)
      (γ₁.comp symbolicConcatenationSecondParameter)
      (symbolicSecondHalfParameter t) = γ₁ t
  by_cases hmem : symbolicSecondHalfParameter t ∈
      (Set.Iic symbolicConcatenationMidpoint)
  · have hp := Set.piecewise_eq_of_mem
      (s := Set.Iic symbolicConcatenationMidpoint)
      (f := (γ₀.comp symbolicConcatenationFirstParameter))
      (g := (γ₁.comp symbolicConcatenationSecondParameter)) hmem
    rw [hp]
    change γ₀ (symbolicConcatenationFirstParameter
      (symbolicSecondHalfParameter t)) = γ₁ t
    have ht : (t : ℝ) ≤ 0 := by
      change (symbolicSecondHalfParameter t : ℝ) ≤
        (symbolicConcatenationMidpoint : ℝ) at hmem
      change (1 + (t : ℝ)) / 2 ≤ 1 / 2 at hmem
      linarith
    have ht0 : (t : ℝ) = 0 := le_antisymm ht t.property.1
    have ht0' : t = (0 : SymbolicPathDomain) := by
      apply Subtype.ext
      exact ht0
    subst t
    simpa [symbolicConcatenationFirstParameter,
      symbolicSecondHalfParameter, symbolicSecondHalfValue,
      symbolicConcatenationMidpoint] using hend
  · have hp := Set.piecewise_eq_of_notMem
      (s := Set.Iic symbolicConcatenationMidpoint)
      (f := (γ₀.comp symbolicConcatenationFirstParameter))
      (g := (γ₁.comp symbolicConcatenationSecondParameter)) hmem
    rw [hp]
    change γ₁ (symbolicConcatenationSecondParameter
      (symbolicSecondHalfParameter t)) = γ₁ t
    congr 1
    apply Subtype.ext
    change max (2 * ((1 + (t : ℝ)) / 2) - 1) 0 = (t : ℝ)
    rw [max_eq_left]
    · ring
    · linarith [t.property.1]

noncomputable def canonicalSymbolicLatentPathConcatenation
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) :
    SymbolicLatentPathConcatenation γ₀ γ₁ :=
  ⟨canonicalSymbolicConcatenation hend,
    ⟨canonicalSymbolicConcatenation_first_half hend,
      canonicalSymbolicConcatenation_second_half hend⟩⟩

theorem canonicalSymbolicConcatenation_start
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) :
    (canonicalSymbolicConcatenation hend).start = γ₀.start := by
  have h := canonicalSymbolicConcatenation_first_half hend
  have h0 := h (0 : SymbolicPathDomain)
  rw [symbolicFirstHalfParameter_zero] at h0
  simpa [SymbolicLatentPath.start] using h0

theorem canonicalSymbolicConcatenation_finish
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) :
    (canonicalSymbolicConcatenation hend).finish = γ₁.finish := by
  have h := canonicalSymbolicConcatenation_second_half hend
  have h1 := h (1 : SymbolicPathDomain)
  rw [symbolicSecondHalfParameter_one] at h1
  simpa [SymbolicLatentPath.finish] using h1

theorem canonicalSymbolicConcatenation_endpoints
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ : SymbolicLatentPath X}
    (hend : γ₀.finish = γ₁.start) :
    (canonicalSymbolicConcatenation hend).endpoints =
      (γ₀.start, γ₁.finish) := by
  ext <;>
    simp [SymbolicLatentPath.endpoints,
      canonicalSymbolicConcatenation_start,
      canonicalSymbolicConcatenation_finish]

end InfoGeometry.Topology

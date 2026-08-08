import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathHomotopyComposition
import InfoGeometry.Topology.SymbolicLatentPathConcatenationConstruction

namespace InfoGeometry.Topology

/-!
# Midpoint gluing of endpoint-preserving path homotopies

This owner supplies the missing property needed for concatenation on homotopy
classes.  The two homotopies are glued in the path coordinate, while their
homotopy coordinate is left untouched.
-/

noncomputable def concatenatedPathHomotopyMap
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₀' γ₁ γ₁' : SymbolicLatentPath X}
    (H₀ : SymbolicLatentPathHomotopy γ₀ γ₀')
    (H₁ : SymbolicLatentPathHomotopy γ₁ γ₁') :
    SymbolicPathSquare → X :=
  by
    classical
    exact Set.piecewise
      (Prod.snd ⁻¹' Set.Iic symbolicConcatenationMidpoint)
      (fun p => H₀.map (p.1, symbolicConcatenationFirstParameter p.2))
      (fun p => H₁.map (p.1, symbolicConcatenationSecondParameter p.2))

theorem concatenatedPathHomotopyMap_continuous
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₀' γ₁ γ₁' : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (_h₀₁' : γ₀'.finish = γ₁'.start)
    (H₀ : SymbolicLatentPathHomotopy γ₀ γ₀')
    (H₁ : SymbolicLatentPathHomotopy γ₁ γ₁') :
    Continuous (concatenatedPathHomotopyMap H₀ H₁) := by
  classical
  let s : Set SymbolicPathSquare :=
    Prod.snd ⁻¹' Set.Iic symbolicConcatenationMidpoint
  let f : SymbolicPathSquare → X :=
    fun p => H₀.map (p.1, symbolicConcatenationFirstParameter p.2)
  let g : SymbolicPathSquare → X :=
    fun p => H₁.map (p.1, symbolicConcatenationSecondParameter p.2)
  have hf : Continuous f := by
    exact H₀.map.continuous.comp
      (continuous_fst.prodMk
        (symbolicConcatenationFirstParameter.continuous.comp continuous_snd))
  have hg : Continuous g := by
    exact H₁.map.continuous.comp
      (continuous_fst.prodMk
        (symbolicConcatenationSecondParameter.continuous.comp continuous_snd))
  have hboundary : ∀ p ∈ frontier s, f p = g p := by
    intro p hp
    have hp' := continuous_snd.frontier_preimage_subset
      (Set.Iic symbolicConcatenationMidpoint) hp
    have hmid : p.2 = symbolicConcatenationMidpoint := by
      apply Subtype.ext
      exact congrArg Subtype.val (Set.mem_singleton_iff.mp
        (frontier_Iic_subset symbolicConcatenationMidpoint hp'))
    change H₀.map (p.1, symbolicConcatenationFirstParameter p.2) =
      H₁.map (p.1, symbolicConcatenationSecondParameter p.2)
    rw [hmid]
    have hfirst : symbolicConcatenationFirstParameter
          symbolicConcatenationMidpoint = (1 : SymbolicPathDomain) := by
      apply Subtype.ext
      norm_num [symbolicConcatenationFirstParameter,
        symbolicConcatenationMidpoint]
    have hsecond : symbolicConcatenationSecondParameter
          symbolicConcatenationMidpoint = (0 : SymbolicPathDomain) := by
      apply Subtype.ext
      norm_num [symbolicConcatenationSecondParameter,
        symbolicConcatenationMidpoint]
    rw [hfirst, hsecond, H₀.fixed_finish, H₁.fixed_start, h₀₁]
  exact hf.piecewise hboundary hg

noncomputable def concatenatedPathHomotopy
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₀' γ₁ γ₁' : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₀₁' : γ₀'.finish = γ₁'.start)
    (H₀ : SymbolicLatentPathHomotopy γ₀ γ₀')
    (H₁ : SymbolicLatentPathHomotopy γ₁ γ₁') :
    SymbolicLatentPathHomotopy
      (canonicalSymbolicConcatenation h₀₁)
      (canonicalSymbolicConcatenation h₀₁') where
  map := {
    toFun := concatenatedPathHomotopyMap H₀ H₁
    continuous_toFun := concatenatedPathHomotopyMap_continuous
      h₀₁ h₀₁' H₀ H₁ }
  at_start := by
    intro t
    by_cases ht : t ∈ Set.Iic symbolicConcatenationMidpoint
    · change concatenatedPathHomotopyMap H₀ H₁ (0, t) = _
      simp [concatenatedPathHomotopyMap, ht]
      rw [H₀.at_start]
      change γ₀ (symbolicConcatenationFirstParameter t) =
        symbolicConcatenationFunction γ₀ γ₁ t
      simp [symbolicConcatenationFunction, ht, Function.comp_def]
    · change concatenatedPathHomotopyMap H₀ H₁ (0, t) = _
      simp [concatenatedPathHomotopyMap, ht]
      rw [H₁.at_start]
      change γ₁ (symbolicConcatenationSecondParameter t) =
        symbolicConcatenationFunction γ₀ γ₁ t
      simp [symbolicConcatenationFunction, ht, Function.comp_def]
  at_finish := by
    intro t
    by_cases ht : t ∈ Set.Iic symbolicConcatenationMidpoint
    · change concatenatedPathHomotopyMap H₀ H₁ (1, t) = _
      simp [concatenatedPathHomotopyMap, ht]
      rw [H₀.at_finish]
      change γ₀' (symbolicConcatenationFirstParameter t) =
        symbolicConcatenationFunction γ₀' γ₁' t
      simp [symbolicConcatenationFunction, ht, Function.comp_def]
    · change concatenatedPathHomotopyMap H₀ H₁ (1, t) = _
      simp [concatenatedPathHomotopyMap, ht]
      rw [H₁.at_finish]
      change γ₁' (symbolicConcatenationSecondParameter t) =
        symbolicConcatenationFunction γ₀' γ₁' t
      simp [symbolicConcatenationFunction, ht, Function.comp_def]
  fixed_start := by
    intro s
    by_cases ht : (0 : SymbolicPathDomain) ∈ Set.Iic symbolicConcatenationMidpoint
    · change concatenatedPathHomotopyMap H₀ H₁ (s, 0) = _
      simp [concatenatedPathHomotopyMap, ht]
      have hzero : symbolicConcatenationFirstParameter
          (0 : SymbolicPathDomain) = 0 := by
        apply Subtype.ext
        norm_num [symbolicConcatenationFirstParameter]
      rw [hzero]
      rw [H₀.fixed_start]
      change γ₀.start =
        (canonicalSymbolicConcatenation h₀₁).start
      exact (canonicalSymbolicLatentPathConcatenation h₀₁).start_eq_first_start.symm
    · norm_num [Set.mem_Iic, symbolicConcatenationMidpoint] at ht
  fixed_finish := by
    intro s
    by_cases ht : (1 : SymbolicPathDomain) ∈ Set.Iic symbolicConcatenationMidpoint
    · change (1 : ℝ) ≤ 1 / 2 at ht
      norm_num at ht
    · change concatenatedPathHomotopyMap H₀ H₁ (s, 1) = _
      simp [concatenatedPathHomotopyMap, ht]
      have hone : symbolicConcatenationSecondParameter
          (1 : SymbolicPathDomain) = 1 := by
        apply Subtype.ext
        norm_num [symbolicConcatenationSecondParameter]
      rw [hone]
      rw [H₁.fixed_finish]
      change γ₁.finish =
        (canonicalSymbolicConcatenation h₀₁).finish
      exact (canonicalSymbolicLatentPathConcatenation h₀₁).finish_eq_second_finish.symm

theorem concatenatedSymbolicPathHomotopic_of_homotopies
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₀' γ₁ γ₁' : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₀₁' : γ₀'.finish = γ₁'.start)
    (H₀ : SymbolicLatentPathHomotopy γ₀ γ₀')
    (H₁ : SymbolicLatentPathHomotopy γ₁ γ₁') :
    SymbolicLatentPathHomotopic
      (canonicalSymbolicConcatenation h₀₁)
      (canonicalSymbolicConcatenation h₀₁') :=
  ⟨concatenatedPathHomotopy h₀₁ h₀₁' H₀ H₁⟩

end InfoGeometry.Topology

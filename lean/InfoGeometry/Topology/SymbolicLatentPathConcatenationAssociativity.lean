import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathConcatenationConstruction
import InfoGeometry.Topology.SymbolicLatentPathReparametrization

namespace InfoGeometry.Topology

/-!
# Parameter change for the two parenthesizations of three paths

The two midpoint parenthesizations use breakpoints `(1/4, 1/2)` and
`(1/2, 3/4)`.  This owner records the explicit endpoint-fixing parameter map
which sends the latter breakpoints to the former ones.  The path-level
associativity theorem is deliberately kept for the next layer; this file
first certifies the parameter geometry it needs.
-/

noncomputable def associativityThreeQuarter : SymbolicPathDomain :=
  ⟨(3 : ℝ) / 4, by constructor <;> norm_num⟩

noncomputable def associativityMiddleParameter :
    C(SymbolicPathDomain, SymbolicPathDomain) :=
  { toFun := fun t =>
      ⟨max ((t : ℝ) - (1 : ℝ) / 4) 0, by
        have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.property.1
        have ht1 : (t : ℝ) ≤ 1 := t.property.2
        constructor
        · exact le_max_right _ _
        · apply max_le
          · linarith
          · norm_num⟩
    continuous_toFun := by
      continuity }

noncomputable def associativityLastParameter :
    C(SymbolicPathDomain, SymbolicPathDomain) :=
  { toFun := fun t =>
      ⟨max (2 * (t : ℝ) - 1) 0, by
        have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.property.1
        have ht1 : (t : ℝ) ≤ 1 := t.property.2
        constructor
        · exact le_max_right _ _
        · apply max_le
          · linarith
          · norm_num⟩
    continuous_toFun := by
      continuity }

noncomputable def associativityParameterFunction (t : SymbolicPathDomain) :
    SymbolicPathDomain :=
  (Set.Iic symbolicConcatenationMidpoint).piecewise
    symbolicFirstHalfParameter
    ((Set.Iic associativityThreeQuarter).piecewise
      associativityMiddleParameter associativityLastParameter) t

theorem associativityParameterFunction_continuous :
    Continuous associativityParameterFunction := by
  let inner : SymbolicPathDomain → SymbolicPathDomain :=
    (Set.Iic associativityThreeQuarter).piecewise
      associativityMiddleParameter associativityLastParameter
  have hinner : Continuous inner := by
    apply continuous_piecewise
    · intro t ht
      have ht' : t = associativityThreeQuarter := by
        exact Subtype.ext (congrArg Subtype.val (Set.mem_singleton_iff.mp
          (frontier_Iic_subset associativityThreeQuarter ht)))
      subst t
      apply Subtype.ext
      norm_num [inner, associativityMiddleParameter,
        associativityLastParameter, associativityThreeQuarter]
    · exact associativityMiddleParameter.continuous.continuousOn
    · exact associativityLastParameter.continuous.continuousOn
  change Continuous ((Set.Iic symbolicConcatenationMidpoint).piecewise
    symbolicFirstHalfParameter inner)
  apply continuous_piecewise
  · intro t ht
    have ht' : t = symbolicConcatenationMidpoint := by
      exact Subtype.ext (congrArg Subtype.val (Set.mem_singleton_iff.mp
        (frontier_Iic_subset symbolicConcatenationMidpoint ht)))
    subst t
    apply Subtype.ext
    norm_num [inner, associativityParameterFunction,
      symbolicFirstHalfParameter, symbolicFirstHalfValue,
      associativityMiddleParameter, associativityLastParameter,
      symbolicConcatenationMidpoint, associativityThreeQuarter]
  · exact symbolicFirstHalfParameter.continuous.continuousOn
  · exact hinner.continuousOn

noncomputable def associativityParameter :
    C(SymbolicPathDomain, SymbolicPathDomain) :=
  { toFun := associativityParameterFunction
    continuous_toFun := associativityParameterFunction_continuous }

theorem associativityParameter_at_zero :
    associativityParameter 0 = (0 : SymbolicPathDomain) := by
  apply Subtype.ext
  norm_num [associativityParameter, associativityParameterFunction,
    symbolicFirstHalfParameter, symbolicFirstHalfValue]

theorem associativityParameter_at_one :
    associativityParameter 1 = (1 : SymbolicPathDomain) := by
  apply Subtype.ext
  change ((Set.Iic symbolicConcatenationMidpoint).piecewise
      symbolicFirstHalfParameter
      ((Set.Iic associativityThreeQuarter).piecewise
        associativityMiddleParameter associativityLastParameter)
      (1 : SymbolicPathDomain) : ℝ) = 1
  rw [Set.piecewise_eq_of_notMem]
  · rw [Set.piecewise_eq_of_notMem]
    · norm_num [associativityParameter, associativityParameterFunction,
        associativityLastParameter]
    · simp only [Set.mem_Iic, not_le]
      change (associativityThreeQuarter : ℝ) < 1
      simpa [associativityThreeQuarter] using
        (show ((3 : ℝ) / 4) < 1 by norm_num)
  · simp only [Set.mem_Iic, not_le]
    change (symbolicConcatenationMidpoint : ℝ) < 1
    simpa [symbolicConcatenationMidpoint] using
      (show ((1 : ℝ) / 2) < 1 by norm_num)

noncomputable def associativityReparametrization :
    SymbolicLatentPathReparametrization :=
  ⟨associativityParameter,
    ⟨associativityParameter_at_zero, associativityParameter_at_one⟩⟩

theorem associativityReparametrization_homotopic
    {X : Type*} [TopologicalSpace X]
    (γ : SymbolicLatentPath X) :
    SymbolicLatentPathHomotopic γ
      (reparametrizeSymbolicLatentPath associativityReparametrization γ) :=
  reparametrizeSymbolicLatentPath_homotopic associativityReparametrization γ

def leftAssociativeEndpoint
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start) :
    (canonicalSymbolicConcatenation h₀₁).finish = γ₂.start := by
  exact (canonicalSymbolicLatentPathConcatenation h₀₁).finish_eq_second_finish.trans h₁₂

def rightAssociativeEndpoint
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start) :
    γ₀.finish = (canonicalSymbolicConcatenation h₁₂).start := by
  exact h₀₁.trans (canonicalSymbolicLatentPathConcatenation h₁₂).start_eq_first_start.symm

noncomputable def leftAssociativeConcatenationPath
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start) : SymbolicLatentPath X :=
  canonicalSymbolicConcatenation (leftAssociativeEndpoint h₀₁ h₁₂)

noncomputable def rightAssociativeConcatenationPath
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start) : SymbolicLatentPath X :=
  canonicalSymbolicConcatenation (rightAssociativeEndpoint h₀₁ h₁₂)

theorem leftAssociativeConcatenationPath_start
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start) :
    (leftAssociativeConcatenationPath h₀₁ h₁₂).start = γ₀.start := by
  exact (canonicalSymbolicLatentPathConcatenation
    (leftAssociativeEndpoint h₀₁ h₁₂)).start_eq_first_start.trans
      (canonicalSymbolicLatentPathConcatenation h₀₁).start_eq_first_start

theorem leftAssociativeConcatenationPath_finish
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start) :
    (leftAssociativeConcatenationPath h₀₁ h₁₂).finish = γ₂.finish := by
  exact (canonicalSymbolicLatentPathConcatenation
    (leftAssociativeEndpoint h₀₁ h₁₂)).finish_eq_second_finish

theorem rightAssociativeConcatenationPath_start
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start) :
    (rightAssociativeConcatenationPath h₀₁ h₁₂).start = γ₀.start := by
  exact (canonicalSymbolicLatentPathConcatenation
    (rightAssociativeEndpoint h₀₁ h₁₂)).start_eq_first_start

theorem rightAssociativeConcatenationPath_finish
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start) :
    (rightAssociativeConcatenationPath h₀₁ h₁₂).finish = γ₂.finish := by
  exact (canonicalSymbolicLatentPathConcatenation
    (rightAssociativeEndpoint h₀₁ h₁₂)).finish_eq_second_finish.trans
      (canonicalSymbolicLatentPathConcatenation h₁₂).finish_eq_second_finish

theorem leftAssociativeConcatenationPath_reparametrization_homotopic
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start) :
    SymbolicLatentPathHomotopic
      (leftAssociativeConcatenationPath h₀₁ h₁₂)
      (reparametrizeSymbolicLatentPath associativityReparametrization
        (leftAssociativeConcatenationPath h₀₁ h₁₂)) :=
  associativityReparametrization_homotopic
    (leftAssociativeConcatenationPath h₀₁ h₁₂)

theorem associativity_reparametrization_first_segment
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start)
    {t : SymbolicPathDomain}
    (ht : t ∈ Set.Iic symbolicConcatenationMidpoint) :
    rightAssociativeConcatenationPath h₀₁ h₁₂ t =
      reparametrizeSymbolicLatentPath associativityReparametrization
        (leftAssociativeConcatenationPath h₀₁ h₁₂) t := by
  change rightAssociativeConcatenationPath h₀₁ h₁₂ t =
    leftAssociativeConcatenationPath h₀₁ h₁₂
      (associativityParameter t)
  have ht_mem : t ∈ Set.Iic symbolicConcatenationMidpoint := ht
  change (t : ℝ) ≤ 1 / 2 at ht
  let u : SymbolicPathDomain := ⟨2 * (t : ℝ), by
    constructor <;> nlinarith [t.property.1, ht]
  ⟩
  have hu : symbolicFirstHalfParameter u = t := by
    apply Subtype.ext
    change (u : ℝ) / 2 = (t : ℝ)
    dsimp [u]
    ring
  have hparam : associativityParameter t =
      symbolicFirstHalfParameter t := by
    apply Subtype.ext
    change ((Set.Iic symbolicConcatenationMidpoint).piecewise
      symbolicFirstHalfParameter
      ((Set.Iic associativityThreeQuarter).piecewise
        associativityMiddleParameter associativityLastParameter) t : ℝ) = _
    rw [Set.piecewise_eq_of_mem _ _ _ ht_mem]
  calc
    rightAssociativeConcatenationPath h₀₁ h₁₂ t =
        rightAssociativeConcatenationPath h₀₁ h₁₂
          (symbolicFirstHalfParameter u) := by rw [hu]
    _ = γ₀ u := by
      exact canonicalSymbolicConcatenation_first_half
        (rightAssociativeEndpoint h₀₁ h₁₂) u
    _ = (canonicalSymbolicConcatenation h₀₁)
          (symbolicFirstHalfParameter u) := by
      exact (canonicalSymbolicConcatenation_first_half h₀₁ u).symm
    _ = (canonicalSymbolicConcatenation h₀₁) t := by rw [hu]
    _ = leftAssociativeConcatenationPath h₀₁ h₁₂
          (symbolicFirstHalfParameter t) := by
      exact (canonicalSymbolicConcatenation_first_half
        (leftAssociativeEndpoint h₀₁ h₁₂) t).symm
    _ = leftAssociativeConcatenationPath h₀₁ h₁₂
          (associativityParameter t) := by rw [hparam]

theorem associativity_reparametrization_middle_segment
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start)
    {t : SymbolicPathDomain}
    (ht₀ : t ∉ Set.Iic symbolicConcatenationMidpoint)
    (ht₁ : t ∈ Set.Iic associativityThreeQuarter) :
    rightAssociativeConcatenationPath h₀₁ h₁₂ t =
      reparametrizeSymbolicLatentPath associativityReparametrization
        (leftAssociativeConcatenationPath h₀₁ h₁₂) t := by
  change rightAssociativeConcatenationPath h₀₁ h₁₂ t =
    leftAssociativeConcatenationPath h₀₁ h₁₂
      (associativityParameter t)
  have ht_low : (1 : ℝ) / 2 < (t : ℝ) := by
    have h : ¬ (t : ℝ) ≤ (1 : ℝ) / 2 := by
      simpa [Set.mem_Iic, symbolicConcatenationMidpoint] using ht₀
    exact lt_of_not_ge h
  have ht_high : (t : ℝ) ≤ (3 : ℝ) / 4 := by
    simpa [Set.mem_Iic, associativityThreeQuarter] using ht₁
  let aR : SymbolicPathDomain := ⟨2 * (t : ℝ) - 1, by
    constructor <;> nlinarith [t.property.1, t.property.2, ht_low]
  ⟩
  let v : SymbolicPathDomain := ⟨4 * (t : ℝ) - 2, by
    constructor <;> nlinarith [t.property.1, t.property.2, ht_low, ht_high]
  ⟩
  let aL : SymbolicPathDomain := ⟨2 * (t : ℝ) - (1 : ℝ) / 2, by
    constructor <;> nlinarith [t.property.1, t.property.2, ht_low, ht_high]
  ⟩
  let s : SymbolicPathDomain := ⟨(t : ℝ) - (1 : ℝ) / 4, by
    constructor <;> nlinarith [t.property.1, t.property.2, ht_low, ht_high]
  ⟩
  have haR : symbolicSecondHalfParameter aR = t := by
    apply Subtype.ext
    change (1 + (aR : ℝ)) / 2 = (t : ℝ)
    dsimp [aR]
    ring
  have hvR : symbolicFirstHalfParameter v = aR := by
    apply Subtype.ext
    change (v : ℝ) / 2 = (aR : ℝ)
    dsimp [v, aR]
    ring
  have hvL : symbolicSecondHalfParameter v = aL := by
    apply Subtype.ext
    change (1 + (v : ℝ)) / 2 = (aL : ℝ)
    dsimp [v, aL]
    ring
  have hsA : symbolicFirstHalfParameter aL = s := by
    apply Subtype.ext
    change (aL : ℝ) / 2 = (s : ℝ)
    dsimp [s, aL]
    ring
  have hparam : associativityParameter t = s := by
    apply Subtype.ext
    change ((Set.Iic symbolicConcatenationMidpoint).piecewise
      symbolicFirstHalfParameter
      ((Set.Iic associativityThreeQuarter).piecewise
        associativityMiddleParameter associativityLastParameter) t : ℝ) = _
    rw [Set.piecewise_eq_of_notMem _ _ _ ht₀]
    rw [Set.piecewise_eq_of_mem _ _ _ ht₁]
    change max ((t : ℝ) - (1 : ℝ) / 4) 0 = (s : ℝ)
    rw [max_eq_left (by linarith [ht_low])]
  calc
    rightAssociativeConcatenationPath h₀₁ h₁₂ t =
        rightAssociativeConcatenationPath h₀₁ h₁₂
          (symbolicSecondHalfParameter aR) := by rw [haR]
    _ = (canonicalSymbolicConcatenation h₁₂) aR := by
      exact canonicalSymbolicConcatenation_second_half
        (rightAssociativeEndpoint h₀₁ h₁₂) aR
    _ = γ₁ v := by
      rw [← hvR]
      exact canonicalSymbolicConcatenation_first_half h₁₂ v
    _ = (canonicalSymbolicConcatenation h₀₁) (symbolicSecondHalfParameter v) := by
      exact (canonicalSymbolicConcatenation_second_half h₀₁ v).symm
    _ = (canonicalSymbolicConcatenation h₀₁) aL := by rw [hvL]
    _ = leftAssociativeConcatenationPath h₀₁ h₁₂
          (symbolicFirstHalfParameter aL) := by
      change (canonicalSymbolicConcatenation h₀₁) aL =
        (canonicalSymbolicConcatenation (leftAssociativeEndpoint h₀₁ h₁₂))
          (symbolicFirstHalfParameter aL)
      exact (canonicalSymbolicConcatenation_first_half
        (leftAssociativeEndpoint h₀₁ h₁₂) aL).symm
    _ = leftAssociativeConcatenationPath h₀₁ h₁₂ s := by rw [hsA]
    _ = leftAssociativeConcatenationPath h₀₁ h₁₂
          (associativityParameter t) := by rw [hparam]

theorem associativity_reparametrization_last_segment
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start)
    {t : SymbolicPathDomain}
    (ht : t ∉ Set.Iic associativityThreeQuarter) :
    rightAssociativeConcatenationPath h₀₁ h₁₂ t =
      reparametrizeSymbolicLatentPath associativityReparametrization
        (leftAssociativeConcatenationPath h₀₁ h₁₂) t := by
  change rightAssociativeConcatenationPath h₀₁ h₁₂ t =
    leftAssociativeConcatenationPath h₀₁ h₁₂
      (associativityParameter t)
  have ht_low : (3 : ℝ) / 4 < (t : ℝ) := by
    have h : ¬ (t : ℝ) ≤ (3 : ℝ) / 4 := by
      simpa [Set.mem_Iic, associativityThreeQuarter] using ht
    exact lt_of_not_ge h
  let aR : SymbolicPathDomain := ⟨2 * (t : ℝ) - 1, by
    constructor <;> nlinarith [t.property.1, t.property.2, ht_low]
  ⟩
  let v : SymbolicPathDomain := ⟨4 * (t : ℝ) - 3, by
    constructor <;> nlinarith [t.property.1, t.property.2, ht_low]
  ⟩
  have haR : symbolicSecondHalfParameter aR = t := by
    apply Subtype.ext
    change (1 + (aR : ℝ)) / 2 = (t : ℝ)
    dsimp [aR]
    ring
  have hvR : symbolicSecondHalfParameter v = aR := by
    apply Subtype.ext
    change (1 + (v : ℝ)) / 2 = (aR : ℝ)
    dsimp [v, aR]
    ring
  have hparam : associativityParameter t = aR := by
    apply Subtype.ext
    change ((Set.Iic symbolicConcatenationMidpoint).piecewise
      symbolicFirstHalfParameter
      ((Set.Iic associativityThreeQuarter).piecewise
        associativityMiddleParameter associativityLastParameter) t : ℝ) = _
    rw [Set.piecewise_eq_of_notMem _ _ _ (by
      intro hmem
      have : (t : ℝ) ≤ (1 : ℝ) / 2 := by
        simpa [Set.mem_Iic, symbolicConcatenationMidpoint] using hmem
      linarith [ht_low])]
    rw [Set.piecewise_eq_of_notMem _ _ _ ht]
    change max (2 * (t : ℝ) - 1) 0 = (aR : ℝ)
    rw [max_eq_left (by linarith [ht_low])]
  calc
    rightAssociativeConcatenationPath h₀₁ h₁₂ t =
        rightAssociativeConcatenationPath h₀₁ h₁₂
          (symbolicSecondHalfParameter aR) := by rw [haR]
    _ = (canonicalSymbolicConcatenation h₁₂) aR := by
      exact canonicalSymbolicConcatenation_second_half
        (rightAssociativeEndpoint h₀₁ h₁₂) aR
    _ = γ₂ v := by
      rw [← hvR]
      exact canonicalSymbolicConcatenation_second_half h₁₂ v
    _ = leftAssociativeConcatenationPath h₀₁ h₁₂
          (symbolicSecondHalfParameter v) := by
      change γ₂ v =
        (canonicalSymbolicConcatenation (leftAssociativeEndpoint h₀₁ h₁₂))
          (symbolicSecondHalfParameter v)
      exact (canonicalSymbolicConcatenation_second_half
        (leftAssociativeEndpoint h₀₁ h₁₂) v).symm
    _ = leftAssociativeConcatenationPath h₀₁ h₁₂ aR := by rw [hvR]
    _ = leftAssociativeConcatenationPath h₀₁ h₁₂
          (associativityParameter t) := by rw [hparam]

theorem rightAssociativeConcatenationPath_eq_reparametrized_left
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start) :
    rightAssociativeConcatenationPath h₀₁ h₁₂ =
      reparametrizeSymbolicLatentPath associativityReparametrization
        (leftAssociativeConcatenationPath h₀₁ h₁₂) := by
  ext t
  by_cases ht₀ : t ∈ Set.Iic symbolicConcatenationMidpoint
  · exact associativity_reparametrization_first_segment h₀₁ h₁₂ ht₀
  · by_cases ht₁ : t ∈ Set.Iic associativityThreeQuarter
    · exact associativity_reparametrization_middle_segment h₀₁ h₁₂ ht₀ ht₁
    · exact associativity_reparametrization_last_segment h₀₁ h₁₂ ht₁

theorem rightAssociativeConcatenationPath_endpoints_eq_left
    {X : Type*} [TopologicalSpace X]
    {γ₀ γ₁ γ₂ : SymbolicLatentPath X}
    (h₀₁ : γ₀.finish = γ₁.start)
    (h₁₂ : γ₁.finish = γ₂.start) :
    (rightAssociativeConcatenationPath h₀₁ h₁₂).endpoints =
      (leftAssociativeConcatenationPath h₀₁ h₁₂).endpoints := by
  rw [rightAssociativeConcatenationPath_eq_reparametrized_left h₀₁ h₁₂]
  ext <;>
    simp [reparametrizeSymbolicLatentPath, SymbolicLatentPath.endpoints,
      SymbolicLatentPath.start, SymbolicLatentPath.finish,
      associativityReparametrization.at_zero,
      associativityReparametrization.at_one]

end InfoGeometry.Topology

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Graph.CategoricalCharacterDistance

/-!
# Complete-case categorical character alignment

Formalizes the marker-retention rule in `dna_character_tree.py`: a marker is
used only when every taxon has an observation and all observations carry the
same algorithm version. Values are compared as categorical states. This file
does not identify structural affinity with ancestry.
-/

namespace InfoGeometry.Graph.CategoricalCharacterAlignment

variable {taxaCount markerCount : ℕ}
variable {State : Type*}

noncomputable section

/-- One observed categorical character together with its digest/encoding
version. -/
structure VersionedCharacter (State : Type*) where
  version : String
  state : State

/-- Snapshot data: a marker may be unobserved for a taxon. -/
abbrev CharacterTable (taxaCount markerCount : ℕ) (State : Type*) :=
  Fin taxaCount → Fin markerCount → Option (VersionedCharacter State)

/-- Whether a marker is observed in every taxon. -/
def markerComplete (table : CharacterTable taxaCount markerCount State)
    (marker : Fin markerCount) : Prop :=
  ∀ taxon, ∃ observation, table taxon marker = some observation

/-- Whether every pair of observations for a marker has the same version. -/
def markerVersionConsistent
    (table : CharacterTable taxaCount markerCount State)
    (marker : Fin markerCount) : Prop :=
  ∀ t₁ t₂ x y, table t₁ marker = some x → table t₂ marker = some y →
    x.version = y.version

/-- Complete-case, version-consistent markers retained by the exporter. -/
def retainedMarkerSet
    (table : CharacterTable taxaCount markerCount State) : Finset (Fin markerCount) := by
  classical
  exact Finset.univ.filter fun marker =>
    markerComplete table marker ∧ markerVersionConsistent table marker

/-- Every retained marker has an observation for each taxon. -/
theorem retained_marker_complete
    (table : CharacterTable taxaCount markerCount State)
    {marker : Fin markerCount} (h : marker ∈ retainedMarkerSet table) :
    ∀ taxon, ∃ observation, table taxon marker = some observation :=
  by
    classical
    exact (Finset.mem_filter.mp h).2.1

/-- Every retained marker uses one shared algorithm version across taxa. -/
theorem retained_marker_version_consistent
    (table : CharacterTable taxaCount markerCount State)
    {marker : Fin markerCount} (h : marker ∈ retainedMarkerSet table) :
    ∀ t₁ t₂ x y, table t₁ marker = some x → table t₂ marker = some y →
      x.version = y.version :=
  by
    classical
    exact (Finset.mem_filter.mp h).2.2

/-- A marker missing from even one taxon is excluded, rather than being
silently interpreted as a zero mismatch or imputed value. -/
theorem marker_excluded_of_missing_observation
    (table : CharacterTable taxaCount markerCount State)
    (marker : Fin markerCount) (taxon : Fin taxaCount)
    (hMissing : table taxon marker = none) :
    marker ∉ retainedMarkerSet table := by
  intro hRetained
  obtain ⟨observation, hObservation⟩ :=
    retained_marker_complete table hRetained taxon
  rw [hMissing] at hObservation
  cases hObservation

/-- A marker with conflicting algorithm versions is excluded even when all
taxa have observations. -/
theorem marker_excluded_of_version_mismatch
    (table : CharacterTable taxaCount markerCount State)
    (marker : Fin markerCount) (t₁ t₂ : Fin taxaCount)
    (x y : VersionedCharacter State)
    (h₁ : table t₁ marker = some x) (h₂ : table t₂ marker = some y)
    (hVersion : x.version ≠ y.version) :
    marker ∉ retainedMarkerSet table := by
  intro hRetained
  exact hVersion (retained_marker_version_consistent table hRetained
    t₁ t₂ x y h₁ h₂)

/-- The aligned categorical profile of one taxon. Excluded markers are set to
`none` for every taxon, so they contribute no mismatches. -/
def alignedProfile
    (table : CharacterTable taxaCount markerCount State)
    (taxon : Fin taxaCount) : Fin markerCount → Option State := by
  classical
  exact fun marker =>
    if marker ∈ retainedMarkerSet table then
      (table taxon marker).map VersionedCharacter.state
    else none

/-- Mismatch count after complete-case and algorithm-version filtering. -/
def alignedMismatchCount
    [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount) : ℕ :=
  InfoGeometry.Graph.CategoricalCharacterDistance.mismatchCount
    (alignedProfile table t₁) (alignedProfile table t₂)

/-- Number of marker columns retained after complete-case and version checks. -/
def retainedMarkerCount
    (table : CharacterTable taxaCount markerCount State) : ℕ :=
  (retainedMarkerSet table).card

/-- The complete categorical column seen across all taxa at one retained
marker. This is the key used by the exporter's `Counter` compression. -/
def retainedMarkerPattern
    (table : CharacterTable taxaCount markerCount State)
    (marker : Fin markerCount) : Fin taxaCount → Option State :=
  fun taxon => alignedProfile table taxon marker

/-- Distinct retained columns, corresponding to the keys of the Python
`Counter` in `dna_character_tree.py`. -/
def retainedPatternSet
    (table : CharacterTable taxaCount markerCount State) : Finset (Fin taxaCount → Option State) := by
  classical
  exact (retainedMarkerSet table).image (retainedMarkerPattern table)

/-- The marker fiber represented by one categorical column. -/
def retainedPatternFiber
    [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (pattern : Fin taxaCount → Option State) : Finset (Fin markerCount) :=
  (retainedMarkerSet table).filter fun marker =>
    retainedMarkerPattern table marker = pattern

/-- Multiplicity of one categorical column among retained markers. -/
def retainedPatternMultiplicity
    [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (pattern : Fin taxaCount → Option State) : ℕ :=
  (retainedPatternFiber table pattern).card

/-- Mismatch count computed from distinct marker patterns and their
frequencies, as in the exporter's `sum(count for pattern if mismatch)`. -/
def patternAggregatedMismatchCount [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount) : ℕ := by
  classical
  exact ∑ pattern ∈ retainedPatternSet table,
    ∑ marker ∈ retainedMarkerSet table with
      retainedMarkerPattern table marker = pattern,
      if alignedProfile table t₁ marker = alignedProfile table t₂ marker then 0 else 1

/-- The literal frequency-weighted form used by the exporter's `Counter`. -/
def patternFrequencyMismatchCount [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount) : ℕ := by
  classical
  exact ∑ pattern ∈ retainedPatternSet table,
    if pattern t₁ = pattern t₂ then 0 else
      retainedPatternMultiplicity table pattern

/-- A `Counter` bucket contributes its frequency precisely when its state at
the two taxa differs. -/
theorem retainedPatternFiber_mismatchCount [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount) (pattern : Fin taxaCount → Option State) :
    (∑ marker ∈ retainedPatternFiber table pattern,
      if alignedProfile table t₁ marker = alignedProfile table t₂ marker then 0 else 1) =
    if pattern t₁ = pattern t₂ then 0 else
      retainedPatternMultiplicity table pattern := by
  classical
  by_cases hEq : pattern t₁ = pattern t₂
  · simp only [ite_eq_left hEq]
    apply Finset.sum_eq_zero
    intro marker hm
    have hPattern := (Finset.mem_filter.mp hm).2
    have h₁ := congrFun hPattern t₁
    have h₂ := congrFun hPattern t₂
    change alignedProfile table t₁ marker = pattern t₁ at h₁
    change alignedProfile table t₂ marker = pattern t₂ at h₂
    simp [h₁, h₂, hEq]
  · simp only [ite_eq_right hEq]
    unfold retainedPatternMultiplicity
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro marker hm
    have hPattern := (Finset.mem_filter.mp hm).2
    have h₁ := congrFun hPattern t₁
    have h₂ := congrFun hPattern t₂
    change alignedProfile table t₁ marker = pattern t₁ at h₁
    change alignedProfile table t₂ marker = pattern t₂ at h₂
    simp [h₁, h₂, hEq]

/-- Replacing each pattern fiber by its frequency gives exactly the grouped
fiber sum. This is the formal `Counter`-compression step in the exporter. -/
theorem patternFrequencyMismatchCount_eq_patternAggregatedMismatchCount
    [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount) :
    patternFrequencyMismatchCount table t₁ t₂ =
      patternAggregatedMismatchCount table t₁ t₂ := by
  classical
  unfold patternFrequencyMismatchCount patternAggregatedMismatchCount
  apply Finset.sum_congr rfl
  intro pattern hp
  rw [← retainedPatternFiber_mismatchCount table t₁ t₂ pattern]
  unfold retainedPatternFiber
  rfl

/-- Within a fixed marker-pattern fiber, the pairwise taxon comparison is
constant. This justifies replacing the fiber sum by its frequency when
implementing the same count with a `Counter`. -/
theorem retainedPatternMismatch_is_constant
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount) {m₁ m₂ : Fin markerCount}
    (hPattern : retainedMarkerPattern table m₁ = retainedMarkerPattern table m₂) :
    (alignedProfile table t₁ m₁ = alignedProfile table t₂ m₁) ↔
      (alignedProfile table t₁ m₂ = alignedProfile table t₂ m₂) := by
  have h₁ := congrFun hPattern t₁
  have h₂ := congrFun hPattern t₂
  change alignedProfile table t₁ m₁ = alignedProfile table t₁ m₂ at h₁
  change alignedProfile table t₂ m₁ = alignedProfile table t₂ m₂ at h₂
  rw [h₁, h₂]

set_option maxHeartbeats 1000000
/-- Grouping retained markers by their complete categorical column does not
change the pairwise mismatch count. This is the finite-sum law behind the
exporter's `Counter`-based distance calculation. -/
theorem patternAggregatedMismatchCount_eq_alignedMismatchCount
    [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount) :
    patternAggregatedMismatchCount table t₁ t₂ =
      alignedMismatchCount table t₁ t₂ := by
  classical
  let s := retainedMarkerSet table
  let f := retainedMarkerPattern table
  let t := s.image f
  have ht : retainedPatternSet table = t := by
    classical
    ext pattern
    simp [retainedPatternSet, s, f, t]
  have hmaps (marker : Fin markerCount) (hm : marker ∈ s) : f marker ∈ t :=
    Finset.mem_image_of_mem f hm
  calc
    patternAggregatedMismatchCount table t₁ t₂ =
        ∑ pattern ∈ t, ∑ marker ∈ s with f marker = pattern,
          if alignedProfile table t₁ marker = alignedProfile table t₂ marker then 0 else 1 := by
          unfold patternAggregatedMismatchCount
          rw [ht]
    _ = ∑ marker ∈ s,
          if alignedProfile table t₁ marker = alignedProfile table t₂ marker then 0 else 1 :=
      Finset.sum_fiberwise_of_maps_to hmaps _
    _ = alignedMismatchCount table t₁ t₂ := by
      unfold alignedMismatchCount
        InfoGeometry.Graph.CategoricalCharacterDistance.mismatchCount
      have hsubset : s ⊆ Finset.univ := Finset.subset_univ _
      rw [Finset.sum_subset hsubset]
      intro marker hmarker hnot
      have hnot' : marker ∉ retainedMarkerSet table := by simpa [s] using hnot
      simp [alignedProfile, hnot']

set_option maxHeartbeats 200000

/-- The exporter's frequency-weighted `Counter` expression agrees with the
direct mismatch count over retained marker columns. -/
theorem patternFrequencyMismatchCount_eq_alignedMismatchCount
    [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount) :
    patternFrequencyMismatchCount table t₁ t₂ =
      alignedMismatchCount table t₁ t₂ := by
  calc
    patternFrequencyMismatchCount table t₁ t₂ =
        patternAggregatedMismatchCount table t₁ t₂ :=
      patternFrequencyMismatchCount_eq_patternAggregatedMismatchCount table t₁ t₂
    _ = alignedMismatchCount table t₁ t₂ :=
      patternAggregatedMismatchCount_eq_alignedMismatchCount table t₁ t₂

/-- Equal-weight categorical mismatch fraction on the actually retained
marker columns, matching the exporter's common denominator. -/
def alignedMismatchFraction [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount)
    (_hRetained : 0 < retainedMarkerCount table) : ℚ :=
  (alignedMismatchCount table t₁ t₂ : ℚ) / (retainedMarkerCount table : ℚ)

/-- The frequency-weighted `Counter` count normalized by the common number of
retained marker columns, matching the pairwise matrix entry in the exporter. -/
def patternFrequencyMismatchFraction [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount)
    (_hRetained : 0 < retainedMarkerCount table) : ℚ :=
  (patternFrequencyMismatchCount table t₁ t₂ : ℚ) /
    (retainedMarkerCount table : ℚ)

/-- Grouping markers into categorical-pattern frequencies and then dividing
by the common retained-marker count yields the same exact rational distance
as comparing the aligned profiles directly. -/
theorem patternFrequencyMismatchFraction_eq_alignedMismatchFraction
    [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount) (hRetained : 0 < retainedMarkerCount table) :
    patternFrequencyMismatchFraction table t₁ t₂ hRetained =
      alignedMismatchFraction table t₁ t₂ hRetained := by
  unfold patternFrequencyMismatchFraction alignedMismatchFraction
  rw [patternFrequencyMismatchCount_eq_alignedMismatchCount]

theorem alignedMismatchCount_le_retainedMarkerCount [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount) :
    alignedMismatchCount table t₁ t₂ ≤ retainedMarkerCount table := by
  classical
  unfold alignedMismatchCount retainedMarkerCount
  unfold InfoGeometry.Graph.CategoricalCharacterDistance.mismatchCount
  calc
    (∑ marker : Fin markerCount,
        if alignedProfile table t₁ marker = alignedProfile table t₂ marker then 0 else 1) ≤
      ∑ marker : Fin markerCount,
        if marker ∈ retainedMarkerSet table then 1 else 0 := by
          apply Finset.sum_le_sum
          intro marker hmarker
          by_cases hret : marker ∈ retainedMarkerSet table
          · simp only [hret, ite_true]
            split <;> omega
          · simp [alignedProfile, hret]
    _ = (retainedMarkerSet table).card := by
      rw [Finset.sum_boole]
      simp [retainedMarkerSet]

theorem alignedMismatchCount_symm
    [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount) :
    alignedMismatchCount table t₁ t₂ = alignedMismatchCount table t₂ t₁ := by
  exact InfoGeometry.Graph.CategoricalCharacterDistance.mismatchCount_symm _ _

theorem alignedMismatchFraction_symm [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount) (hRetained : 0 < retainedMarkerCount table) :
    alignedMismatchFraction table t₁ t₂ hRetained =
      alignedMismatchFraction table t₂ t₁ hRetained := by
  unfold alignedMismatchFraction
  rw [alignedMismatchCount_symm]

theorem alignedMismatchFraction_nonneg [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount) (hRetained : 0 < retainedMarkerCount table) :
    0 ≤ alignedMismatchFraction table t₁ t₂ hRetained := by
  unfold alignedMismatchFraction
  positivity

/-- With at least one retained marker, zero mismatch fraction means exactly
that the two taxa have the same aligned categorical profile. -/
theorem alignedMismatchFraction_eq_zero_iff [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount) (hRetained : 0 < retainedMarkerCount table) :
    alignedMismatchFraction table t₁ t₂ hRetained = 0 ↔
      alignedProfile table t₁ = alignedProfile table t₂ := by
  have hDen : (retainedMarkerCount table : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hRetained)
  constructor
  · intro hFrac
    have hCountRat : (alignedMismatchCount table t₁ t₂ : ℚ) = 0 :=
      (div_eq_zero_iff).mp (by simpa [alignedMismatchFraction] using hFrac)
        |>.resolve_right hDen
    have hCount : alignedMismatchCount table t₁ t₂ = 0 := by
      exact_mod_cast hCountRat
    exact (InfoGeometry.Graph.CategoricalCharacterDistance.mismatchCount_eq_zero_iff
      (alignedProfile table t₁) (alignedProfile table t₂)).mp hCount
  · intro hProfile
    have hCount : alignedMismatchCount table t₁ t₂ = 0 :=
      (InfoGeometry.Graph.CategoricalCharacterDistance.mismatchCount_eq_zero_iff
        (alignedProfile table t₁) (alignedProfile table t₂)).mpr hProfile
    simp [alignedMismatchFraction, hCount]

/-- The retained-marker mismatch fraction lies in `[0,1]` whenever at least
one comparable marker survives filtering. -/
theorem alignedMismatchFraction_le_one [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ : Fin taxaCount) (hRetained : 0 < retainedMarkerCount table) :
    alignedMismatchFraction table t₁ t₂ hRetained ≤ 1 := by
  have hNum : (alignedMismatchCount table t₁ t₂ : ℚ) ≤
      (retainedMarkerCount table : ℚ) := by
    exact_mod_cast alignedMismatchCount_le_retainedMarkerCount table t₁ t₂
  have hDen : (0 : ℚ) < (retainedMarkerCount table : ℚ) := by
    exact_mod_cast hRetained
  unfold alignedMismatchFraction
  apply (div_le_iff₀ hDen).2
  simpa using hNum

theorem alignedMismatchCount_triangle
    [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ t₃ : Fin taxaCount) :
    alignedMismatchCount table t₁ t₃ ≤
      alignedMismatchCount table t₁ t₂ + alignedMismatchCount table t₂ t₃ := by
  exact InfoGeometry.Graph.CategoricalCharacterDistance.mismatchCount_triangle _ _ _

/-- Triangle inequality for the complete-case categorical mismatch fraction;
all three distances use the same retained-marker denominator. -/
theorem alignedMismatchFraction_triangle [DecidableEq State]
    (table : CharacterTable taxaCount markerCount State)
    (t₁ t₂ t₃ : Fin taxaCount)
    (hRetained : 0 < retainedMarkerCount table) :
    alignedMismatchFraction table t₁ t₃ hRetained ≤
      alignedMismatchFraction table t₁ t₂ hRetained +
        alignedMismatchFraction table t₂ t₃ hRetained := by
  have hCount := alignedMismatchCount_triangle table t₁ t₂ t₃
  have hDen : (0 : ℚ) < (retainedMarkerCount table : ℚ) := by
    exact_mod_cast hRetained
  unfold alignedMismatchFraction
  rw [← add_div]
  apply (div_le_div_iff_of_pos_right hDen).2
  exact_mod_cast hCount

end
end InfoGeometry.Graph.CategoricalCharacterAlignment

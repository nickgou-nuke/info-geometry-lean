import InfoGeometry.Canonical.RealStagePrefixProjectionTopological
import InfoGeometry.Canonical.CantorBoundaryDyadicCover
import InfoGeometry.Canonical.RealUHFProjectionRankCompletionReadoutSquare

/-!
# Explicit dyadic readouts of finite prefix-rank projections

This owner records the actual points produced by the finite prefix projections.
It does not identify their range with the full real interval; that density
statement requires a separate representation theorem.
-/

noncomputable section

open scoped Topology

namespace InfoGeometry.Canonical

open CategoryTheory
open UHFInductiveColimitBoundary
open RealUHFProjectionRankRealCompletionTopological
open RealUHFProjectionRankTailSystem
open RealUHFProjectionRankIntervalTopological
open RealUHFProjectionRankCompletionReadoutSquare
open CantorBoundaryDyadicCover
open CantorBoundaryFiniteReadout

abbrev PrefixRankParameter :=
  Σ n : ℕ, {r : ℕ // r ≤ 2 ^ n}

def prefixRankDyadicPoint (p : PrefixRankParameter) :
    {q : ℚ // q ∈ Set.Icc (0 : ℚ) 1} :=
  ⟨(p.2.1 : ℚ) / (2 : ℚ) ^ p.1,
    ⟨by positivity,
      by
        have hr : (p.2.1 : ℚ) ≤ (2 ^ p.1 : ℕ) := by
          exact_mod_cast p.2.2
        have hpow : (0 : ℚ) < (2 : ℚ) ^ p.1 := by positivity
        apply (div_le_one hpow).2
        simpa using hr⟩⟩

def prefixRankReadout (p : PrefixRankParameter) : RealUnitInterval :=
  prefixTailSystem p.1 p.2.1 p.2.2 |>.realReadout 0

theorem prefixRankReadout_value (p : PrefixRankParameter) :
    (prefixRankReadout p : ℝ) =
      (((p.2.1 : ℚ) / (2 : ℚ) ^ p.1 : ℚ) : ℝ) := by
  unfold prefixRankReadout
  exact prefixTailSystem_realReadout_value p.1 p.2.1 p.2.2 0

theorem prefixRankDyadicPoint_value (p : PrefixRankParameter) :
    (prefixRankDyadicPoint p : ℚ) =
      (dyadicStageMap p.1 (p.2.1 : ℤ) : ℚ) := by
  rfl

  theorem prefixRankReadout_real_eq_directLimit_stage
    (p : PrefixRankParameter) :
    (((dyadicDirectLimitEquiv
        (dyadicStage p.1 (p.2.1 : ℤ)) : DyadicRational) : ℚ) : ℝ) =
      (prefixRankReadout p : ℝ) := by
  change (((dyadicStageMap p.1 (p.2.1 : ℤ) : DyadicRational) : ℚ) : ℝ) =
    (prefixRankReadout p : ℝ)
  rw [prefixRankReadout_value]
  simp [dyadicStageMap]

noncomputable def prefixRankCompatibleIntervalReadout
    (p : PrefixRankParameter) : CompatibleIntervalReadout :=
  ⟨fun _ => prefixRankDyadicPoint p, by
    intro k
    rfl⟩

@[simp] theorem prefixRankCompatibleIntervalReadout_coordinate
    (p : PrefixRankParameter) (k : ℕ) :
    (prefixRankCompatibleIntervalReadout p).1 k =
      prefixRankDyadicPoint p := rfl

theorem prefixRankCompatibleIntervalReadout_real_coordinate
    (p : PrefixRankParameter) (k : ℕ) :
    dyadicToRealInterval
        ((prefixRankCompatibleIntervalReadout p).1 k) =
      prefixRankReadout p := by
  apply Subtype.ext
  simp only [prefixRankCompatibleIntervalReadout_coordinate,
    dyadicToRealInterval]
  exact (prefixRankReadout_value p).symm

theorem prefixRankReadout_eq_dyadicToRealInterval (p : PrefixRankParameter) :
    prefixRankReadout p = dyadicToRealInterval (prefixRankDyadicPoint p) := by
  apply Subtype.ext
  simp only [dyadicToRealInterval]
  exact prefixRankReadout_value p

theorem prefixRankReadout_mem_realUnitInterval (p : PrefixRankParameter) :
    (prefixRankReadout p : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
  (prefixRankReadout p).property

def listBinaryNumerator : List Bool → ℕ
  | [] => 0
  | b :: bs =>
      (if b then 2 ^ bs.length else 0) + listBinaryNumerator bs

theorem finitePrefixReadout_eq_listBinaryNumerator_div
    (bs : List Bool) :
    finitePrefixReadout bs =
      (listBinaryNumerator bs : ℝ) / (2 : ℝ) ^ bs.length := by
  induction bs with
  | nil => simp [finitePrefixReadout, listBinaryNumerator]
  | cons b bs ih =>
      simp only [finitePrefixReadout, listBinaryNumerator, List.length_cons]
      rw [ih]
      by_cases hb : b <;> simp [hb, pow_succ]
      <;> field_simp

theorem listBinaryNumerator_le_pow_length (bs : List Bool) :
    listBinaryNumerator bs ≤ 2 ^ bs.length := by
  induction bs with
  | nil => simp [listBinaryNumerator]
  | cons b bs ih =>
      simp only [listBinaryNumerator, List.length_cons]
      by_cases hb : b <;> simp [hb, pow_succ] at * <;> omega

def wordBinaryNumerator {n : ℕ} (w : BitWord n) : ℕ :=
  listBinaryNumerator (List.ofFn w)

theorem wordBinaryNumerator_le (n : ℕ) (w : BitWord n) :
    wordBinaryNumerator w ≤ 2 ^ n := by
  simpa [wordBinaryNumerator] using
    listBinaryNumerator_le_pow_length (List.ofFn w)

theorem prefixRankReadout_of_word
    {n : ℕ} (w : BitWord n) :
    prefixRankReadout
        ⟨n, ⟨wordBinaryNumerator w, wordBinaryNumerator_le n w⟩⟩ =
      finitePrefixReadout (List.ofFn w) := by
  rw [prefixRankReadout_value]
  rw [finitePrefixReadout_eq_listBinaryNumerator_div]
  simp [wordBinaryNumerator]

theorem denseRange_prefixRankReadout :
    DenseRange prefixRankReadout := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  have hpow : Filter.Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N)
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hpow) ε hε
  have hpowN : (1 / 2 : ℝ) ^ N < ε := by
    have hN' := hN N (le_rfl)
    rw [Real.dist_eq] at hN'
    simpa [abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N by positivity)]
      using hN'
  obtain ⟨w, hw⟩ := exists_prefix_dyadic_cover x.1 x.2 N
  let p : PrefixRankParameter :=
    ⟨N, ⟨wordBinaryNumerator w, wordBinaryNumerator_le N w⟩⟩
  refine ⟨p, ?_⟩
  have hp : prefixRankReadout p =
      finitePrefixReadout (List.ofFn w) := by
    exact prefixRankReadout_of_word w
  change dist x.1 (prefixRankReadout p : ℝ) < ε
  rw [hp]
  rw [Real.dist_eq, abs_of_nonneg (by linarith [hw.1])]
  linarith [hw.2, hpowN]

noncomputable def prefixRankCompatibleIntervalReadoutTopCatHom :
    TopCat.of PrefixRankParameter ⟶ TopCat.of CompatibleIntervalReadout :=
  TopCat.ofHom
    { toFun := prefixRankCompatibleIntervalReadout
      continuous_toFun := continuous_of_discreteTopology }

@[simp] theorem prefixRankCompatibleIntervalReadoutTopCatHom_apply
    (p : PrefixRankParameter) :
    prefixRankCompatibleIntervalReadoutTopCatHom p =
      prefixRankCompatibleIntervalReadout p := rfl

noncomputable def prefixRankReadoutTopCatHom :
    TopCat.of PrefixRankParameter ⟶ TopCat.of RealUnitInterval :=
  TopCat.ofHom
    { toFun := prefixRankReadout
      continuous_toFun := continuous_of_discreteTopology }

@[simp] theorem prefixRankReadoutTopCatHom_apply
    (p : PrefixRankParameter) :
    prefixRankReadoutTopCatHom p = prefixRankReadout p := rfl

theorem prefixRankReadoutTopCatHom_factorization
    (p : PrefixRankParameter) :
    prefixRankReadoutTopCatHom p =
      dyadicToRealInterval
        ((prefixRankCompatibleIntervalReadoutTopCatHom p).1 0) := by
  exact (prefixRankCompatibleIntervalReadout_real_coordinate p 0).symm

theorem prefixRank_completion_readout_square :
    prefixRankCompatibleIntervalReadoutTopCatHom ≫
        compatibleToRealIntervalTopCatHom =
      prefixRankReadoutTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app]
  change compatibleToRealInterval
      (prefixRankCompatibleIntervalReadout p) =
    prefixRankReadout p
  exact prefixRankCompatibleIntervalReadout_real_coordinate p 0

noncomputable def compatibleIntervalReadoutHomeomorphTopCatHom :
    TopCat.of CompatibleIntervalReadout ⟶ TopCat.of DyadicUnitInterval :=
  TopCat.ofHom
    { toFun := compatibleIntervalReadoutHomeomorph
      continuous_toFun := compatibleIntervalReadoutHomeomorph.continuous }

noncomputable def prefixRankDyadicTopCatHom :
    TopCat.of PrefixRankParameter ⟶ TopCat.of DyadicUnitInterval :=
  TopCat.ofHom
    { toFun := prefixRankDyadicPoint
      continuous_toFun := continuous_of_discreteTopology }

@[simp] theorem prefixRankDyadicTopCatHom_apply
    (p : PrefixRankParameter) :
    prefixRankDyadicTopCatHom p = prefixRankDyadicPoint p := rfl

theorem prefixRank_dyadic_topcat_factorization :
    prefixRankCompatibleIntervalReadoutTopCatHom ≫
        compatibleIntervalReadoutHomeomorphTopCatHom =
      prefixRankDyadicTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app]
  rfl

theorem denseRange_prefixRankDyadicPoint :
    DenseRange prefixRankDyadicPoint := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  have hx : (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨by exact_mod_cast x.property.1,
      by exact_mod_cast x.property.2⟩
  have hpow : Filter.Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N)
      Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hpow) ε hε
  have hpowN : (1 / 2 : ℝ) ^ N < ε := by
    have hN' := hN N (le_rfl)
    rw [Real.dist_eq] at hN'
    simpa [abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N by positivity)]
      using hN'
  obtain ⟨w, hw⟩ := exists_prefix_dyadic_cover (x : ℝ) hx N
  let p : PrefixRankParameter :=
    ⟨N, ⟨wordBinaryNumerator w, wordBinaryNumerator_le N w⟩⟩
  refine ⟨p, ?_⟩
  have hp : (prefixRankDyadicPoint p : ℝ) =
      finitePrefixReadout (List.ofFn w) := by
    calc
      (prefixRankDyadicPoint p : ℝ) =
          (prefixRankReadout p : ℝ) := by
            exact congrArg Subtype.val
              (prefixRankReadout_eq_dyadicToRealInterval p).symm
      _ = finitePrefixReadout (List.ofFn w) := by
        exact prefixRankReadout_of_word w
  change dist (x : ℝ) (prefixRankDyadicPoint p : ℝ) < ε
  rw [hp, Real.dist_eq, abs_of_nonneg (by linarith [hw.1])]
  linarith [hw.2, hpowN]

theorem denseRange_prefixRankDyadicTopCatHom :
    DenseRange prefixRankDyadicTopCatHom := by
  simpa only [prefixRankDyadicTopCatHom_apply] using
    denseRange_prefixRankDyadicPoint

theorem prefixRankDyadicPoint_mem_closure_range
    (x : {q : ℚ // q ∈ Set.Icc (0 : ℚ) 1}) :
    x ∈ closure (Set.range prefixRankDyadicPoint) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p, hp⟩ :=
    (Metric.denseRange_iff.mp denseRange_prefixRankDyadicPoint) x ε hε
  exact ⟨prefixRankDyadicPoint p, ⟨p, rfl⟩, hp⟩

theorem closure_range_prefixRankDyadicPoint :
    closure (Set.range prefixRankDyadicPoint) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact prefixRankDyadicPoint_mem_closure_range x

theorem prefixRankReadout_mem_closure_range
    (x : RealUnitInterval) :
    x ∈ closure (Set.range prefixRankReadout) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p, hp⟩ :=
    (Metric.denseRange_iff.mp denseRange_prefixRankReadout) x ε hε
  exact ⟨prefixRankReadout p, ⟨p, rfl⟩, hp⟩

theorem closure_range_prefixRankReadout :
    closure (Set.range prefixRankReadout) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact prefixRankReadout_mem_closure_range x

theorem closure_range_prefixRankDyadicTopCatHom :
    closure (Set.range prefixRankDyadicTopCatHom) = Set.univ := by
  simpa only [prefixRankDyadicTopCatHom_apply] using
    closure_range_prefixRankDyadicPoint

end InfoGeometry.Canonical

end

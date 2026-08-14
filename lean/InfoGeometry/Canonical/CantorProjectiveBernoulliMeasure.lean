import Mathlib.MeasureTheory.Measure.Map
import InfoGeometry.Analysis.FractalMeasure.Basic
import InfoGeometry.Canonical.RindlerMobiusCantorFiniteBridge
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit

/-!
# Bernoulli measure on the Cantor projective limit

The fair product measure on binary streams is transported through the concrete
projective-limit homeomorphism.  The resulting measure has the exact finite
prefix masses required by the cylinder KMS recursion.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure

open scoped ENNReal
open MeasureTheory
open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Analysis.FractalMeasure.Basic
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit
open InfoGeometry.Canonical.CuntzCantorBoundaryShift
open InfoGeometry.Canonical.RindlerMobiusCantorFiniteBridge
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology

instance : MeasurableSpace PrefixProjectiveLimit :=
  borel PrefixProjectiveLimit

instance : BorelSpace PrefixProjectiveLimit :=
  ⟨rfl⟩

def projectiveLimitMeasure : Measure PrefixProjectiveLimit :=
  Measure.map PrefixProjectiveLimit.ofCantor fractalMeasure

/-! An explicit interface for the native categorical prefix limit.  The
measurable structure is kept local to the measure definition rather than
installed as a global wrapper instance. -/
abbrev NativePrefixLimit := PrefixProjectiveLimit

noncomputable def boundaryNativeLimitHomeomorph :
    (ℕ → Bool) ≃ₜ NativePrefixLimit :=
  cantorHomeomorphPrefixProjectiveLimit

noncomputable def nativeProjectiveBernoulliMeasure :
    Measure NativePrefixLimit :=
  projectiveLimitMeasure

instance projectiveLimitMeasure_isProbabilityMeasure :
    IsProbabilityMeasure projectiveLimitMeasure := by
  unfold projectiveLimitMeasure
  exact Measure.isProbabilityMeasure_map
    PrefixProjectiveLimit.continuous_ofCantor.measurable.aemeasurable

theorem boundaryNativeLimitHomeomorph_measurePreserving :
    MeasurePreserving boundaryNativeLimitHomeomorph
      fractalMeasure nativeProjectiveBernoulliMeasure := by
  refine ⟨boundaryNativeLimitHomeomorph.continuous.measurable, ?_⟩
  rfl

/-! The prepend branch is a depth-one cylinder for the native Bernoulli
measure. -/
theorem fractalMeasure_prependBit_range (b : Bool) :
    fractalMeasure (Set.range (prependBit b)) = (1 / 2 : ℝ≥0∞) := by
  have hrange :
      Set.range (prependBit b) =
        InfoGeometry.Analysis.FractalMeasure.Basic.cylinderSet
          (Finset.range 1) (fun _ : ℕ => b) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩ i hi
      have hi' : i < 1 := Finset.mem_range.mp hi
      have hi0 : i = 0 := by omega
      subst i
      simp [prependBit]
    · intro hx
      refine ⟨tail x, ?_⟩
      apply prependBit_tail_of_head
      have hx0 := hx 0 (by simp)
      simpa [prependBit] using hx0
  rw [hrange, measure_cylinderSet]
  simp

theorem topologyCylinderSet_eq_coordinateCylinder
    (n : ℕ) (w : BitWord n) :
    InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.cylinderSet n w =
      InfoGeometry.Analysis.FractalMeasure.Basic.cylinderSet
        (Finset.range n)
        (fun i => if hi : i < n then w ⟨i, hi⟩ else false) := by
  let f : ℕ → Bool := fun i => if hi : i < n then w ⟨i, hi⟩ else false
  ext x
  constructor
  · intro hx
    change InfoGeometry.Canonical.UHFInductiveColimitBoundary.boundaryPrefix n x = w at hx
    intro i hi
    have hiN : i < n := Finset.mem_range.mp hi
    have hxi := congrFun hx ⟨i, hiN⟩
    simpa [f, hiN,
      InfoGeometry.Canonical.UHFInductiveColimitBoundary.boundaryPrefix] using hxi
  · intro hx
    change InfoGeometry.Canonical.UHFInductiveColimitBoundary.boundaryPrefix n x = w
    funext i
    have hiN : i < n := i.isLt
    have hxi := hx i.1 (Finset.mem_range.mpr hiN)
    simpa [f, hiN,
      InfoGeometry.Canonical.UHFInductiveColimitBoundary.boundaryPrefix] using hxi

theorem fractalMeasure_topologyCylinderSet
    (n : ℕ) (w : BitWord n) :
    fractalMeasure
        (InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.cylinderSet n w) =
      (1 / 2 : ℝ≥0∞) ^ n := by
  rw [topologyCylinderSet_eq_coordinateCylinder]
  simpa using measure_cylinderSet (Finset.range n)
    (fun i => if hi : i < n then w ⟨i, hi⟩ else false)

theorem fractalMeasure_prependBit_image_cylinder
    (n : ℕ) (b : Bool) (w : BitWord n) :
    fractalMeasure
        (prependBit b ''
          InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.cylinderSet n w) =
      (1 / 2 : ℝ≥0∞) ^ (n + 1) := by
  rw [InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.cylinderSet_prependBit_image]
  exact fractalMeasure_topologyCylinderSet (n + 1)
    (InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.prependWord n b w)

theorem fractalMeasure_prependBit_image_cylinder_eq_half_mul
    (n : ℕ) (b : Bool) (w : BitWord n) :
    fractalMeasure
        (prependBit b ''
          InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.cylinderSet n w) =
      (1 / 2 : ℝ≥0∞) *
        fractalMeasure
          (InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology.cylinderSet n w) := by
  rw [fractalMeasure_prependBit_image_cylinder,
    fractalMeasure_topologyCylinderSet]
  rw [pow_succ]
  ring

theorem projectiveLimitMeasure_apply_prefix_fiber
    (N : ℕ) (b : BitWord N) :
    projectiveLimitMeasure {q : PrefixProjectiveLimit | q.π N = b} =
      (1 / 2 : ℝ≥0∞) ^ N := by
  let f : ℕ → Bool := fun i => if hi : i < N then b ⟨i, hi⟩ else false
  have hfiber :
      PrefixProjectiveLimit.ofCantor ⁻¹'
          {q : PrefixProjectiveLimit | q.π N = b} =
        InfoGeometry.Analysis.FractalMeasure.Basic.cylinderSet
          (Finset.range N) f := by
    ext x
    constructor
    · intro hx
      change PrefixProjectiveLimit.π N (PrefixProjectiveLimit.ofCantor x) = b at hx
      have hcoord := congrFun hx
      intro i hi
      have hiN : i < N := Finset.mem_range.mp hi
      have hxi := hcoord ⟨i, hiN⟩
      simpa [PrefixProjectiveLimit.π, PrefixProjectiveLimit.ofCantor,
        boundaryPrefix, f, hiN] using hxi
    · intro hx
      change PrefixProjectiveLimit.π N (PrefixProjectiveLimit.ofCantor x) = b
      funext i
      have hiN : i < N := i.2
      have hmem : i.1 ∈ Finset.range N := Finset.mem_range.mpr hiN
      have hxi := hx i.1 hmem
      simpa [PrefixProjectiveLimit.π, PrefixProjectiveLimit.ofCantor,
        boundaryPrefix, f, hiN] using hxi
  obtain ⟨p, hp⟩ := projectiveLimit_prefix_fiber_nonempty N b
  have hclosed : IsClosed {q : PrefixProjectiveLimit | q.π N = b} := by
    rw [← hp]
    exact projectiveLimit_prefix_fiber_isClosed p N
  rw [projectiveLimitMeasure, Measure.map_apply
    PrefixProjectiveLimit.continuous_ofCantor.measurable
    hclosed.measurableSet]
  rw [hfiber]
  simpa using measure_cylinderSet (Finset.range N) f

theorem projectiveLimit_prefix_fiber_readout_pair_bound
    (N : ℕ) (b : BitWord N)
    {p q : PrefixProjectiveLimit}
    (hp : p.π N = b) (hq : q.π N = b) :
    |realBinaryReadout (toCantor p) - realBinaryReadout (toCantor q)| ≤
      (1 / 2 : ℝ) ^ N := by
  apply projectiveLimit_prefix_readout_control N p q
  exact hp.trans hq.symm

theorem projectiveLimit_prefix_fiber_mass_and_readout_control
    (N : ℕ) (b : BitWord N) :
    projectiveLimitMeasure {q : PrefixProjectiveLimit | q.π N = b} =
        (1 / 2 : ℝ≥0∞) ^ N ∧
      ∀ {p q : PrefixProjectiveLimit},
        p.π N = b → q.π N = b →
          |realBinaryReadout (toCantor p) - realBinaryReadout (toCantor q)| ≤
            (1 / 2 : ℝ) ^ N := by
  refine ⟨projectiveLimitMeasure_apply_prefix_fiber N b, ?_⟩
  intro p q hp hq
  exact projectiveLimit_prefix_fiber_readout_pair_bound N b hp hq

theorem tomita_measure_image_prefix_fiber
    (N : ℕ) (b : BitWord N) :
    projectiveLimitMeasure
        (tomitaProjectiveLimit ''
          {q : PrefixProjectiveLimit | q.π N = b}) =
      projectiveLimitMeasure {q : PrefixProjectiveLimit | q.π N = b} := by
  obtain ⟨p, hp⟩ := projectiveLimit_prefix_fiber_nonempty N b
  have hset :
      tomitaProjectiveLimit ''
          {q : PrefixProjectiveLimit | q.π N = b} =
        {q : PrefixProjectiveLimit | q.π N = (tomitaProjectiveLimit p).π N} := by
    rw [← hp]
    exact tomitaProjectiveLimit_maps_prefix_fiber p N
  rw [hset, projectiveLimitMeasure_apply_prefix_fiber,
    projectiveLimitMeasure_apply_prefix_fiber]

theorem projectiveLimitMeasure_prefix_successor_additive
    (N : ℕ) (b : BitWord N) :
    projectiveLimitMeasure {q : PrefixProjectiveLimit | q.π N = b} =
      projectiveLimitMeasure
          {q : PrefixProjectiveLimit | q.π (N + 1) = extendSucc N b false} +
        projectiveLimitMeasure
          {q : PrefixProjectiveLimit | q.π (N + 1) = extendSucc N b true} := by
  rw [projectiveLimitMeasure_apply_prefix_fiber,
    projectiveLimitMeasure_apply_prefix_fiber,
    projectiveLimitMeasure_apply_prefix_fiber]
  rw [pow_succ]
  rw [← mul_add]
  have h : (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := by
    rw [ENNReal.div_eq_inv_mul]
    simp only [mul_one]
    have h2 : (2 : ℝ≥0∞)⁻¹ * 2 = 1 :=
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    rw [← two_mul, mul_comm 2 (2 : ℝ≥0∞)⁻¹, h2]
  rw [h, mul_one]

theorem projectiveLimitMeasure_apply_prefix_successor_fiber
    (N : ℕ) (b : BitWord N) (c : Bool) :
    projectiveLimitMeasure
        {q : PrefixProjectiveLimit |
          q.π (N + 1) = extendSucc N b c} =
      (1 / 2) ^ (N + 1) := by
  exact projectiveLimitMeasure_apply_prefix_fiber
    (N + 1) (extendSucc N b c)

theorem projectiveLimitMeasure_prefix_successor_half_parent
    (N : ℕ) (b : BitWord N) (c : Bool) :
    projectiveLimitMeasure
        {q : PrefixProjectiveLimit |
          q.π (N + 1) = extendSucc N b c} =
      (1 / 2 : ℝ≥0∞) *
        projectiveLimitMeasure
          {q : PrefixProjectiveLimit | q.π N = b} := by
  rw [projectiveLimitMeasure_apply_prefix_successor_fiber,
    projectiveLimitMeasure_apply_prefix_fiber, pow_succ]
  ring

theorem projectiveLimit_prefix_fiber_successor_union
    (N : ℕ) (b : BitWord N) :
    {q : PrefixProjectiveLimit | q.π N = b} =
      {q : PrefixProjectiveLimit | q.π (N + 1) = extendSucc N b false} ∪
        {q : PrefixProjectiveLimit | q.π (N + 1) = extendSucc N b true} := by
  ext q
  constructor
  · intro hq
    let c : Bool := q.π (N + 1) ⟨N, Nat.lt_succ_self N⟩
    cases hc : c with
    | false =>
        left
        change q.π (N + 1) = extendSucc N b false
        funext i
        by_cases hi : i.1 < N
        · have hcoh := congrFun (q.projection_coherent N) ⟨i.1, hi⟩
          have hbase := congrFun hq ⟨i.1, hi⟩
          simpa [prefixSucc, extendSucc, hi] using hcoh.trans hbase
        · have hiN : i.1 = N := by omega
          have hiEq : i = ⟨N, Nat.lt_succ_self N⟩ := by
            ext
            exact hiN
          rw [hiEq]
          simpa [c, extendSucc] using hc
    | true =>
        right
        change q.π (N + 1) = extendSucc N b true
        funext i
        by_cases hi : i.1 < N
        · have hcoh := congrFun (q.projection_coherent N) ⟨i.1, hi⟩
          have hbase := congrFun hq ⟨i.1, hi⟩
          simpa [prefixSucc, extendSucc, hi] using hcoh.trans hbase
        · have hiN : i.1 = N := by omega
          have hiEq : i = ⟨N, Nat.lt_succ_self N⟩ := by
            ext
            exact hiN
          rw [hiEq]
          simpa [c, extendSucc] using hc
  · intro hq
    rcases hq with hq | hq
    · change q.π N = b
      rw [← q.projection_coherent N, hq, prefixSucc_extendSucc]
    · change q.π N = b
      rw [← q.projection_coherent N, hq, prefixSucc_extendSucc]

theorem projectiveLimit_prefix_successor_fibers_disjoint
    (N : ℕ) (b : BitWord N) :
    Disjoint
      {q : PrefixProjectiveLimit | q.π (N + 1) = extendSucc N b false}
      {q : PrefixProjectiveLimit | q.π (N + 1) = extendSucc N b true} := by
  apply projectiveLimit_prefix_fiber_pairwise_disjoint (N + 1)
  intro h
  have hcoord := congrFun h ⟨N, Nat.lt_succ_self N⟩
  simpa [extendSucc] using hcoord

theorem projectiveLimit_prefix_successor_measure_union
    (N : ℕ) (b : BitWord N) :
    projectiveLimitMeasure
        ({q : PrefixProjectiveLimit |
            q.π (N + 1) = extendSucc N b false} ∪
          {q : PrefixProjectiveLimit |
            q.π (N + 1) = extendSucc N b true}) =
      projectiveLimitMeasure
        {q : PrefixProjectiveLimit |
          q.π (N + 1) = extendSucc N b false} +
      projectiveLimitMeasure
        {q : PrefixProjectiveLimit |
          q.π (N + 1) = extendSucc N b true} := by
  have hnonempty : ∀ c : Bool, ∃ p : PrefixProjectiveLimit,
      p.π (N + 1) = extendSucc N b c := by
    intro c
    exact projectiveLimit_prefix_fiber_nonempty (N + 1)
      (extendSucc N b c)
  have hclosed : ∀ c : Bool, IsClosed
      {q : PrefixProjectiveLimit |
        q.π (N + 1) = extendSucc N b c} := by
    intro c
    obtain ⟨p, hp⟩ := hnonempty c
    rw [← hp]
    exact projectiveLimit_prefix_fiber_isClosed p (N + 1)
  exact MeasureTheory.measure_union
    (projectiveLimit_prefix_successor_fibers_disjoint N b)
    (hclosed true).measurableSet

theorem projectiveLimitMeasure_prefix_successor_union_eq_parent
    (N : ℕ) (b : BitWord N) :
    projectiveLimitMeasure
        ({q : PrefixProjectiveLimit |
            q.π (N + 1) = extendSucc N b false} ∪
          {q : PrefixProjectiveLimit |
            q.π (N + 1) = extendSucc N b true}) =
      projectiveLimitMeasure {q : PrefixProjectiveLimit | q.π N = b} := by
  calc
    projectiveLimitMeasure
          ({q : PrefixProjectiveLimit |
              q.π (N + 1) = extendSucc N b false} ∪
            {q : PrefixProjectiveLimit |
              q.π (N + 1) = extendSucc N b true}) =
        projectiveLimitMeasure
            {q : PrefixProjectiveLimit |
              q.π (N + 1) = extendSucc N b false} +
          projectiveLimitMeasure
            {q : PrefixProjectiveLimit |
              q.π (N + 1) = extendSucc N b true} :=
      projectiveLimit_prefix_successor_measure_union N b
    _ = projectiveLimitMeasure {q : PrefixProjectiveLimit | q.π N = b} :=
      (projectiveLimitMeasure_prefix_successor_additive N b).symm

def projectiveLimitReadoutMeasure : Measure ℝ :=
  Measure.map
    (fun p : PrefixProjectiveLimit => realBinaryReadout (toCantor p))
    projectiveLimitMeasure

instance projectiveLimitReadoutMeasure_isProbabilityMeasure :
    IsProbabilityMeasure projectiveLimitReadoutMeasure := by
  unfold projectiveLimitReadoutMeasure
  exact Measure.isProbabilityMeasure_map
    continuous_projectiveLimit_readout.measurable.aemeasurable

theorem projectiveLimitReadoutMeasure_apply_compl_unitInterval :
    projectiveLimitReadoutMeasure (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [projectiveLimitReadoutMeasure, Measure.map_apply
    continuous_projectiveLimit_readout.measurable
    measurableSet_Icc.compl]
  have hpre :
      (fun p : PrefixProjectiveLimit => realBinaryReadout (toCantor p)) ⁻¹'
          (Set.Icc (0 : ℝ) 1)ᶜ = ∅ := by
    ext p
    constructor
    · intro hp
      have hreadout := projectiveLimit_readout_image_subset_unitInterval
        ⟨p, rfl⟩
      exact (hp hreadout).elim
    · intro hp
      exact False.elim (by simpa using hp)
  rw [hpre, measure_empty]

theorem projectiveLimitReadoutMeasure_apply_unitInterval :
    projectiveLimitReadoutMeasure (Set.Icc (0 : ℝ) 1) = 1 := by
  have hcompl := measure_compl (μ := projectiveLimitReadoutMeasure)
    (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc (measure_ne_top _ _)
  rw [projectiveLimitReadoutMeasure_apply_compl_unitInterval] at hcompl
  have hcompl' : (1 : ℝ≥0∞) -
      projectiveLimitReadoutMeasure (Set.Icc (0 : ℝ) 1) = 0 := by
    simpa [MeasureTheory.IsProbabilityMeasure.measure_univ] using hcompl.symm
  have hlower : (1 : ℝ≥0∞) ≤
      projectiveLimitReadoutMeasure (Set.Icc (0 : ℝ) 1) :=
    (tsub_eq_zero_iff_le.mp hcompl')
  have hupper : projectiveLimitReadoutMeasure (Set.Icc (0 : ℝ) 1) ≤ 1 := by
    have h := measure_mono (μ := projectiveLimitReadoutMeasure)
      (Set.subset_univ (Set.Icc (0 : ℝ) 1))
    simpa [MeasureTheory.IsProbabilityMeasure.measure_univ] using h
  exact le_antisymm hupper hlower

/-- The projective-limit readout regarded as a map into the closed unit interval. -/
def projectiveLimitUnitIntervalReadout
    (p : PrefixProjectiveLimit) : Set.Icc (0 : ℝ) 1 :=
  ⟨realBinaryReadout (toCantor p),
    projectiveLimit_readout_image_subset_unitInterval ⟨p, rfl⟩⟩

theorem continuous_projectiveLimitUnitIntervalReadout :
    Continuous projectiveLimitUnitIntervalReadout := by
  exact continuous_projectiveLimit_readout.subtype_mk (fun p =>
    projectiveLimit_readout_image_subset_unitInterval ⟨p, rfl⟩)

def projectiveLimitUnitIntervalMeasure :
    Measure (Set.Icc (0 : ℝ) 1) :=
  Measure.map projectiveLimitUnitIntervalReadout projectiveLimitMeasure

instance projectiveLimitUnitIntervalMeasure_isProbabilityMeasure :
    IsProbabilityMeasure projectiveLimitUnitIntervalMeasure := by
  unfold projectiveLimitUnitIntervalMeasure
  exact Measure.isProbabilityMeasure_map
    continuous_projectiveLimitUnitIntervalReadout.measurable.aemeasurable

theorem projectiveLimitUnitIntervalMeasure_map_subtypeVal :
    Measure.map (fun x : Set.Icc (0 : ℝ) 1 => (x : ℝ))
        projectiveLimitUnitIntervalMeasure =
      projectiveLimitReadoutMeasure := by
  unfold projectiveLimitUnitIntervalMeasure projectiveLimitReadoutMeasure
  rw [Measure.map_map (μ := projectiveLimitMeasure)
    (f := projectiveLimitUnitIntervalReadout)
    (g := fun x : Set.Icc (0 : ℝ) 1 => (x : ℝ))
    continuous_subtype_val.measurable
    continuous_projectiveLimitUnitIntervalReadout.measurable]
  rfl

theorem projectiveLimitUnitIntervalMeasure_integral_comp
    (φ : Set.Icc (0 : ℝ) 1 → ℝ)
    (hφ : AEStronglyMeasurable φ projectiveLimitUnitIntervalMeasure) :
    (∫ x, φ x ∂projectiveLimitUnitIntervalMeasure) =
      ∫ p, φ (projectiveLimitUnitIntervalReadout p) ∂projectiveLimitMeasure := by
  exact MeasureTheory.integral_map
    continuous_projectiveLimitUnitIntervalReadout.measurable.aemeasurable hφ

theorem projectiveLimitUnitIntervalMeasure_continuous_integral_comp
    (φ : Set.Icc (0 : ℝ) 1 → ℝ)
    (hφ : Continuous φ) (C : ℝ)
    (hC : ∀ x, ‖φ x‖ ≤ C) :
    Integrable φ projectiveLimitUnitIntervalMeasure ∧
      (∫ x, φ x ∂projectiveLimitUnitIntervalMeasure) =
        ∫ p, φ (projectiveLimitUnitIntervalReadout p) ∂projectiveLimitMeasure := by
  have hstrong : AEStronglyMeasurable φ projectiveLimitUnitIntervalMeasure :=
    hφ.aestronglyMeasurable
  have hint : Integrable φ projectiveLimitUnitIntervalMeasure :=
    Integrable.of_bound hstrong C (ae_of_all _ hC)
  exact ⟨hint, projectiveLimitUnitIntervalMeasure_integral_comp φ hstrong⟩

def tomitaSymmetrizedMeasure : Measure PrefixProjectiveLimit :=
  (1 / 2 : ℝ≥0∞) •
    (projectiveLimitMeasure +
      Measure.map tomitaProjectiveLimit projectiveLimitMeasure)

instance tomitaSymmetrizedMeasure_isProbabilityMeasure :
    IsProbabilityMeasure tomitaSymmetrizedMeasure := by
  refine ⟨?_⟩
  unfold tomitaSymmetrizedMeasure
  rw [Measure.smul_apply, Measure.add_apply]
  rw [Measure.map_apply continuous_tomitaProjectiveLimit.measurable
    MeasurableSet.univ]
  simp [MeasureTheory.IsProbabilityMeasure.measure_univ]
  have htwo : (1 : ℝ≥0∞) + 1 = 2 := by norm_num
  have hinv : (2 : ℝ≥0∞)⁻¹ * 2 = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  rw [htwo, hinv]

theorem tomita_measure_preserving_symmetrized :
    Measure.map tomitaProjectiveLimit tomitaSymmetrizedMeasure =
      tomitaSymmetrizedMeasure := by
  unfold tomitaSymmetrizedMeasure
  have hmeas : Measurable tomitaProjectiveLimit :=
    continuous_tomitaProjectiveLimit.measurable
  rw [Measure.map_smul, Measure.map_add _ _ hmeas]
  have hmap :
      Measure.map tomitaProjectiveLimit
          (Measure.map tomitaProjectiveLimit projectiveLimitMeasure) =
        Measure.map (tomitaProjectiveLimit ∘ tomitaProjectiveLimit)
          projectiveLimitMeasure :=
    Measure.map_map (μ := projectiveLimitMeasure)
      (g := tomitaProjectiveLimit) (f := tomitaProjectiveLimit) hmeas hmeas
  rw [hmap]
  have hinv : tomitaProjectiveLimit ∘ tomitaProjectiveLimit = id := by
    funext p
    exact tomitaProjectiveLimit_involutive p
  rw [hinv, Measure.map_id]
  rw [add_comm]

def tomitaSymmetrizedReadoutMeasure : Measure ℝ :=
  Measure.map
    (fun p : PrefixProjectiveLimit => realBinaryReadout (toCantor p))
    tomitaSymmetrizedMeasure

instance tomitaSymmetrizedReadoutMeasure_isProbabilityMeasure :
    IsProbabilityMeasure tomitaSymmetrizedReadoutMeasure := by
  unfold tomitaSymmetrizedReadoutMeasure
  exact Measure.isProbabilityMeasure_map
    continuous_projectiveLimit_readout.measurable.aemeasurable

def readoutTomitaReflection : ℝ → ℝ := fun x => 1 - x

theorem readout_tomita_reflection_intertwines :
    (fun p : PrefixProjectiveLimit =>
        readoutTomitaReflection
          (realBinaryReadout (toCantor p))) =
      (fun p : PrefixProjectiveLimit =>
        realBinaryReadout (toCantor (tomitaProjectiveLimit p))) := by
  funext p
  unfold readoutTomitaReflection
  have h := projectiveLimit_tomita_real_readout_affine p
  linarith

theorem tomita_measure_preserving_symmetrized_readout :
    Measure.map readoutTomitaReflection tomitaSymmetrizedReadoutMeasure =
      tomitaSymmetrizedReadoutMeasure := by
  have hreadout : Measurable
      (fun p : PrefixProjectiveLimit =>
        realBinaryReadout (toCantor p)) :=
    continuous_projectiveLimit_readout.measurable
  have hreflection : Measurable readoutTomitaReflection := by
    exact (continuous_const.sub continuous_id).measurable
  have htomita : Measurable tomitaProjectiveLimit :=
    continuous_tomitaProjectiveLimit.measurable
  have hcomp :
      readoutTomitaReflection ∘
          (fun p : PrefixProjectiveLimit =>
            realBinaryReadout (toCantor p)) =
        (fun p : PrefixProjectiveLimit =>
          realBinaryReadout (toCantor (tomitaProjectiveLimit p))) := by
    simpa [Function.comp_def] using readout_tomita_reflection_intertwines
  unfold tomitaSymmetrizedReadoutMeasure
  rw [Measure.map_map hreflection hreadout]
  rw [hcomp]
  have hcomp₂ :
      (fun p : PrefixProjectiveLimit =>
          realBinaryReadout (toCantor (tomitaProjectiveLimit p))) =
        (fun p : PrefixProjectiveLimit =>
          realBinaryReadout (toCantor p)) ∘ tomitaProjectiveLimit := by
    rfl
  rw [hcomp₂]
  rw [← Measure.map_map hreadout htomita]
  rw [tomita_measure_preserving_symmetrized]

theorem tomitaSymmetrizedReadoutMeasure_apply_compl_unitInterval :
    tomitaSymmetrizedReadoutMeasure (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  unfold tomitaSymmetrizedReadoutMeasure
  rw [Measure.map_apply continuous_projectiveLimit_readout.measurable
    measurableSet_Icc.compl]
  have hpre :
      (fun p : PrefixProjectiveLimit =>
          realBinaryReadout (toCantor p)) ⁻¹'
          (Set.Icc (0 : ℝ) 1)ᶜ = ∅ := by
    ext p
    constructor
    · intro hp
      have hreadout := projectiveLimit_readout_image_subset_unitInterval
        ⟨p, rfl⟩
      exact (hp hreadout).elim
    · intro hp
      exact False.elim (by simpa using hp)
  rw [hpre, measure_empty]

theorem tomitaSymmetrizedReadoutMeasure_apply_unitInterval :
    tomitaSymmetrizedReadoutMeasure (Set.Icc (0 : ℝ) 1) = 1 := by
  have hcompl := measure_compl (μ := tomitaSymmetrizedReadoutMeasure)
    (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc (measure_ne_top _ _)
  rw [tomitaSymmetrizedReadoutMeasure_apply_compl_unitInterval] at hcompl
  have hcompl' : (1 : ℝ≥0∞) -
      tomitaSymmetrizedReadoutMeasure (Set.Icc (0 : ℝ) 1) = 0 := by
    simpa [MeasureTheory.IsProbabilityMeasure.measure_univ] using hcompl.symm
  have hlower : (1 : ℝ≥0∞) ≤
      tomitaSymmetrizedReadoutMeasure (Set.Icc (0 : ℝ) 1) :=
    (tsub_eq_zero_iff_le.mp hcompl')
  have hupper : tomitaSymmetrizedReadoutMeasure (Set.Icc (0 : ℝ) 1) ≤ 1 := by
    have h := measure_mono (μ := tomitaSymmetrizedReadoutMeasure)
      (Set.subset_univ (Set.Icc (0 : ℝ) 1))
    simpa [MeasureTheory.IsProbabilityMeasure.measure_univ] using h
  exact le_antisymm hupper hlower

theorem tomitaSymmetrizedReadoutMeasure_integrable_id :
    Integrable (fun x : ℝ => x) tomitaSymmetrizedReadoutMeasure := by
  have hstrong : AEStronglyMeasurable (fun x : ℝ => x)
      tomitaSymmetrizedReadoutMeasure :=
    measurable_id.aemeasurable.aestronglyMeasurable
  have hmem : ∀ᵐ x ∂tomitaSymmetrizedReadoutMeasure,
      x ∈ Set.Icc (0 : ℝ) 1 := by
    exact mem_ae_iff.mpr
      tomitaSymmetrizedReadoutMeasure_apply_compl_unitInterval
  apply Integrable.of_bound hstrong 1
  filter_upwards [hmem] with x hx
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem tomitaSymmetrizedReadoutMeasure_integral_id_eq_half :
    ∫ x : ℝ, x ∂tomitaSymmetrizedReadoutMeasure = 1 / 2 := by
  let μ := tomitaSymmetrizedReadoutMeasure
  have hμ : Integrable (fun x : ℝ => x) μ := by
    exact tomitaSymmetrizedReadoutMeasure_integrable_id
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) μ :=
    integrable_const 1
  have href :
      ∫ x : ℝ, x ∂Measure.map readoutTomitaReflection μ =
        ∫ x : ℝ, x ∂μ := by
    rw [tomita_measure_preserving_symmetrized_readout]
  have hmap := MeasureTheory.integral_map
    (μ := μ) (φ := readoutTomitaReflection)
    (continuous_const.sub continuous_id).measurable.aemeasurable
    measurable_id.aemeasurable.aestronglyMeasurable
  have hsub :
      ∫ x : ℝ, x ∂μ = ∫ x : ℝ, (1 - x) ∂μ := by
    rw [← href]
    simpa [readoutTomitaReflection] using hmap
  have hsub' := integral_sub hconst hμ
  have hconst_int : ∫ _x : ℝ, (1 : ℝ) ∂μ = 1 := by
    simp [MeasureTheory.IsProbabilityMeasure.measure_univ]
  have hrelation :
      (∫ x : ℝ, x ∂μ) = 1 - ∫ x : ℝ, x ∂μ := by
    calc
      (∫ x : ℝ, x ∂μ) = ∫ x : ℝ, (1 - x) ∂μ := hsub
      _ = (∫ x : ℝ, (1 : ℝ) ∂μ) - ∫ x : ℝ, x ∂μ := hsub'
      _ = 1 - ∫ x : ℝ, x ∂μ := by rw [hconst_int]
  have hhalf : (∫ x : ℝ, x ∂μ) = 1 / 2 := by
    linarith
  simpa [μ] using hhalf

theorem tomitaSymmetrizedReadoutMeasure_integral_one_sub_id_eq_half :
    ∫ x : ℝ, (1 - x) ∂tomitaSymmetrizedReadoutMeasure = 1 / 2 := by
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ))
      tomitaSymmetrizedReadoutMeasure := integrable_const 1
  have hid : Integrable (fun x : ℝ => x)
      tomitaSymmetrizedReadoutMeasure :=
    tomitaSymmetrizedReadoutMeasure_integrable_id
  rw [integral_sub hconst hid]
  simp [MeasureTheory.IsProbabilityMeasure.measure_univ,
    tomitaSymmetrizedReadoutMeasure_integral_id_eq_half]
  norm_num

end InfoGeometry.Canonical.CantorProjectiveBernoulliMeasure

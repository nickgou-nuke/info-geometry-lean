import InfoGeometry.Canonical.RindlerMobiusLogDeRhamBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorBoundaryFinitePrecision
import InfoGeometry.Canonical.CantorBoundaryReadoutComplexRealBridge
import InfoGeometry.Canonical.CantorProjectiveLimit
import InfoGeometry.Canonical.CantorProjectiveReadoutBridge
import InfoGeometry.Canonical.CantorCylinderTopology
import InfoGeometry.Canonical.CantorBoundaryCuntzShift
import InfoGeometry.Projective.KleinQuadricMonodromy
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Tactic

/-!
# Finite Rindler--Möbius and binary-boundary bridge

This owner connects already-proved finite pieces.  It does not identify a
positive modular logarithm with a Maurer--Cartan form.  The logarithmic split
is stated at the scalar complex level, while the phase period is the genuine
`1/z` de Rham period on the deleted divisor.
-/

noncomputable section

namespace InfoGeometry.Canonical.RindlerMobiusCantorFiniteBridge

open scoped BigOperators Topology
open Set Filter TopologicalSpace
open InfoGeometry.Canonical.RindlerMobiusLogDeRhamBridge
open InfoGeometry.Dynamics.RindlerWedge
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryFinitePrecision
open InfoGeometry.Canonical.CantorBoundaryComplexReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutComplexRealBridge
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds

local instance : T2Space ℝ := TopologicalSpace.t2Space_of_metrizableSpace
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorCylinderTopology
open InfoGeometry.Canonical.CantorBoundaryCuntzShift
open InfoGeometry.Projective.KleinQuadric.DeRhamMonodromy
open Set Filter

/-! ## Scalar logarithmic split -/

theorem complex_log_real_imag_split (z : ℂ) :
    (Complex.log z).re = Real.log ‖z‖ ∧
      (Complex.log z).im = Complex.arg z := by
  exact ⟨Complex.log_re z, Complex.log_im z⟩

theorem rinder_projective_log_split (c : RindlerCoordinates) :
    (Complex.log (complexProjectiveNullRatio c)).re =
        Real.log (rindlerProjectiveNullRatio c) ∧
      (Complex.log (complexProjectiveNullRatio c)).im = 0 := by
  have hpos : 0 < rindlerProjectiveNullRatio c := by
    rw [rindlerProjectiveNullRatio_eq_exp]
    positivity
  have hlog := complex_log_real_imag_split (complexProjectiveNullRatio c)
  rw [hlog.1, hlog.2]
  constructor
  · simp [complexProjectiveNullRatio, Real.norm_eq_abs, abs_of_pos hpos]
  · have harg := Complex.arg_ofReal_of_nonneg (le_of_lt hpos)
    simpa [complexProjectiveNullRatio] using harg

/-! ## Prefix approximants form a genuine Cauchy sequence -/

theorem realBinaryPartialReadout_cauchy
    (w : InfiniteBinaryWordSpace) :
    CauchySeq (fun N : ℕ => realBinaryPartialReadout N w) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hlim := realBinaryPartialReadout_tendsto_readout w
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) (ε / 2) (half_pos hε)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hm' := hN m hm
  have hn' := hN n hn
  calc
    dist (realBinaryPartialReadout m w) (realBinaryPartialReadout n w) ≤
        dist (realBinaryPartialReadout m w) (realBinaryReadout w) +
          dist (realBinaryReadout w) (realBinaryPartialReadout n w) :=
      dist_triangle _ _ _
    _ = |realBinaryPartialReadout m w - realBinaryReadout w| +
          |realBinaryReadout w - realBinaryPartialReadout n w| := by
      rw [Real.dist_eq, Real.dist_eq]
    _ < ε := by
      have hm_abs :
          |realBinaryPartialReadout m w - realBinaryReadout w| < ε / 2 := by
        simpa [Real.dist_eq] using hm'
      have hn_abs :
          |realBinaryReadout w - realBinaryPartialReadout n w| < ε / 2 := by
        simpa [Real.dist_eq, abs_sub_comm] using hn'
      linarith

theorem finite_prefixes_cauchy_basis
    (w : InfiniteBinaryWordSpace) :
    ∀ ε > 0, ∃ N, ∀ v,
      (∀ n < N, v n = w n) →
        |realBinaryReadout v - realBinaryReadout w| < ε := by
  intro ε hε
  have hpow : Filter.Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hpow) ε hε
  refine ⟨N, fun v hv => ?_⟩
  exact lt_of_le_of_lt
    (by
      simpa [abs_sub_comm] using
        (real_readout_prefix_stability N w v (fun n hn => (hv n hn).symm)))
    (by
      have h := hN N le_rfl
      rw [Real.dist_eq] at h
      simpa [abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N by positivity)] using h)

/-! ## Projective-limit compatibility of the readout -/

theorem projectiveLimit_prefix_readout_control
    (N : ℕ) (p q : PrefixProjectiveLimit)
    (hprefix : p.π N = q.π N) :
    |realBinaryReadout (toCantor p) - realBinaryReadout (toCantor q)| ≤
      (1 / 2 : ℝ) ^ N := by
  apply real_readout_prefix_stability N (toCantor p) (toCantor q)
  intro n hn
  have hp := congrFun (boundaryPrefix_toCantor_eq_word p N) ⟨n, hn⟩
  have hq := congrFun (boundaryPrefix_toCantor_eq_word q N) ⟨n, hn⟩
  have hcoord : p.word N ⟨n, hn⟩ = q.word N ⟨n, hn⟩ :=
    congrFun hprefix ⟨n, hn⟩
  exact hp.trans (hcoord.trans hq.symm)

theorem projectiveLimit_prefix_readout_uniform_precision
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ p q : PrefixProjectiveLimit,
      p.π N = q.π N →
        |realBinaryReadout (toCantor p) - realBinaryReadout (toCantor q)| < ε := by
  have hpow : Filter.Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hpow) ε hε
  refine ⟨N, fun p q hprefix => lt_of_le_of_lt
    (projectiveLimit_prefix_readout_control N p q hprefix) ?_⟩
  have h := hN N le_rfl
  rw [Real.dist_eq] at h
  simpa [abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ N by positivity)] using h

theorem projectiveLimit_partialReadout_eq_of_prefix
    (N : ℕ) (p q : PrefixProjectiveLimit)
    (hprefix : p.π N = q.π N) :
    realBinaryPartialReadout N (toCantor p) =
      realBinaryPartialReadout N (toCantor q) := by
  apply realBinaryPartialReadout_congr_of_prefix N (toCantor p) (toCantor q)
  intro n hn
  have hp := congrFun (boundaryPrefix_toCantor_eq_word p N) ⟨n, hn⟩
  have hq := congrFun (boundaryPrefix_toCantor_eq_word q N) ⟨n, hn⟩
  have hcoord : p.word N ⟨n, hn⟩ = q.word N ⟨n, hn⟩ :=
    congrFun hprefix ⟨n, hn⟩
  exact hp.trans (hcoord.trans hq.symm)

theorem projectiveLimit_partialReadout_tendsto
    (p : PrefixProjectiveLimit) :
    Filter.Tendsto
      (fun N => realBinaryPartialReadout N (toCantor p))
      Filter.atTop
      (nhds (realBinaryReadout (toCantor p))) := by
  exact realBinaryPartialReadout_tendsto_readout (toCantor p)

/-! ## Cuntz branch readouts -/

theorem realBinaryReadout_leftShift (w : InfiniteBinaryWordSpace) :
    realBinaryReadout (leftShift w) =
      (1 / 2 : ℝ) * realBinaryReadout w := by
  simpa [leftShift, prefixBit, boundaryCons] using
    (realBinaryReadout_boundaryCons false w)

theorem realBinaryReadout_rightShift (w : InfiniteBinaryWordSpace) :
    realBinaryReadout (rightShift w) =
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * realBinaryReadout w := by
  simpa [rightShift, prefixBit, boundaryCons] using
    (realBinaryReadout_boundaryCons true w)

theorem projectiveLimit_readout_leftShift (p : PrefixProjectiveLimit) :
    realBinaryReadout (leftShift (toCantor p)) =
      (1 / 2 : ℝ) * realBinaryReadout (toCantor p) := by
  exact realBinaryReadout_leftShift (toCantor p)

theorem projectiveLimit_readout_rightShift (p : PrefixProjectiveLimit) :
    realBinaryReadout (rightShift (toCantor p)) =
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * realBinaryReadout (toCantor p) := by
  exact realBinaryReadout_rightShift (toCantor p)

def leftShiftProjectiveLimit (p : PrefixProjectiveLimit) : PrefixProjectiveLimit :=
  PrefixProjectiveLimit.ofCantor (leftShift (toCantor p))

def rightShiftProjectiveLimit (p : PrefixProjectiveLimit) : PrefixProjectiveLimit :=
  PrefixProjectiveLimit.ofCantor (rightShift (toCantor p))

theorem continuous_leftShift : Continuous (leftShift : InfiniteBinaryWordSpace →
    InfiniteBinaryWordSpace) := by
  change Continuous (fun x : InfiniteBinaryWordSpace =>
    fun n => prefixBit false x n)
  exact continuous_pi fun n => by
    cases n with
    | zero => exact continuous_const
    | succ n => exact continuous_apply n

theorem continuous_rightShift : Continuous (rightShift : InfiniteBinaryWordSpace →
    InfiniteBinaryWordSpace) := by
  change Continuous (fun x : InfiniteBinaryWordSpace =>
    fun n => prefixBit true x n)
  exact continuous_pi fun n => by
    cases n with
    | zero => exact continuous_const
    | succ n => exact continuous_apply n

theorem continuous_leftShiftProjectiveLimit :
    Continuous leftShiftProjectiveLimit := by
  exact PrefixProjectiveLimit.continuous_ofCantor.comp
    (continuous_leftShift.comp PrefixProjectiveLimit.continuous_toCantor)

theorem continuous_rightShiftProjectiveLimit :
    Continuous rightShiftProjectiveLimit := by
  exact PrefixProjectiveLimit.continuous_ofCantor.comp
    (continuous_rightShift.comp PrefixProjectiveLimit.continuous_toCantor)

@[simp] theorem toCantor_leftShiftProjectiveLimit (p : PrefixProjectiveLimit) :
    toCantor (leftShiftProjectiveLimit p) = leftShift (toCantor p) := by
  exact PrefixProjectiveLimit.toCantor_ofCantor _

@[simp] theorem toCantor_rightShiftProjectiveLimit (p : PrefixProjectiveLimit) :
    toCantor (rightShiftProjectiveLimit p) = rightShift (toCantor p) := by
  exact PrefixProjectiveLimit.toCantor_ofCantor _

theorem projectiveLimit_leftShift_readout (p : PrefixProjectiveLimit) :
    realBinaryReadout (toCantor (leftShiftProjectiveLimit p)) =
      (1 / 2 : ℝ) * realBinaryReadout (toCantor p) := by
  rw [toCantor_leftShiftProjectiveLimit]
  exact realBinaryReadout_leftShift (toCantor p)

theorem projectiveLimit_rightShift_readout (p : PrefixProjectiveLimit) :
    realBinaryReadout (toCantor (rightShiftProjectiveLimit p)) =
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * realBinaryReadout (toCantor p) := by
  rw [toCantor_rightShiftProjectiveLimit]
  exact realBinaryReadout_rightShift (toCantor p)

theorem continuous_projectiveLimit_readout :
    Continuous (fun p : PrefixProjectiveLimit =>
      realBinaryReadout (toCantor p)) := by
  exact continuous_realBinaryReadout.comp continuous_toCantor

theorem projectiveLimit_readout_image_subset_unitInterval :
    Set.range (fun p : PrefixProjectiveLimit =>
      realBinaryReadout (toCantor p)) ⊆ Set.Icc (0 : ℝ) 1 := by
  rintro _ ⟨p, rfl⟩
  exact realBinaryReadout_mem_unitInterval (toCantor p)

theorem continuous_projectiveLimit_partialReadout (N : ℕ) :
    Continuous (fun p : PrefixProjectiveLimit =>
      realBinaryPartialReadout N (toCantor p)) := by
  exact continuous_realBinaryPartialReadout N |>.comp continuous_toCantor

theorem projectiveLimit_ext_of_all_prefixes
    {p q : PrefixProjectiveLimit}
    (h : ∀ N, p.π N = q.π N) :
    p = q := by
  apply PrefixProjectiveLimit.ext
  funext N
  exact h N

theorem initialSegment_cylinders_nhds_basis
    (x : InfiniteBinaryWordSpace) :
    (nhds x).HasBasis (fun _ : ℕ => True)
      (fun N => initialSegmentCylinder x N) := by
  apply (nhds_hasBasis_finiteCoordinateCylinder x).to_hasBasis
  · intro s hs
    obtain ⟨M, hM⟩ := hs.exists_le
    refine ⟨M + 1, trivial, ?_⟩
    intro y hy
    intro i hi
    exact (mem_initialSegmentCylinder x y (M + 1)).mp hy i
      (lt_of_le_of_lt (hM i hi) (Nat.lt_succ_self M))
  · intro N _
    refine ⟨initialSegmentSet N, initialSegmentSet_finite N, ?_⟩
    intro y hy
    exact hy

theorem projectiveLimit_prefix_fiber_isOpen
    (p : PrefixProjectiveLimit) (N : ℕ) :
    IsOpen {q : PrefixProjectiveLimit | q.π N = p.π N} := by
  change IsOpen ((π N) ⁻¹' ({p.π N} : Set _))
  exact (continuous_π N).isOpen_preimage _ (isOpen_discrete _)

theorem projectiveLimit_prefix_fiber_isClosed
    (p : PrefixProjectiveLimit) (N : ℕ) :
    IsClosed {q : PrefixProjectiveLimit | q.π N = p.π N} := by
  change IsClosed ((π N) ⁻¹' ({p.π N} : Set _))
  exact IsClosed.preimage (continuous_π N) (isClosed_discrete _)

theorem projectiveLimit_prefix_fiber_isClopen
    (p : PrefixProjectiveLimit) (N : ℕ) :
    IsClopen {q : PrefixProjectiveLimit | q.π N = p.π N} :=
  ⟨projectiveLimit_prefix_fiber_isClosed p N,
    projectiveLimit_prefix_fiber_isOpen p N⟩

theorem projectiveLimit_prefix_fiber_iInter_singleton
    (p : PrefixProjectiveLimit) :
    (⋂ N : ℕ, {q : PrefixProjectiveLimit | q.π N = p.π N}) = {p} := by
  ext q
  simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    exact projectiveLimit_ext_of_all_prefixes h
  · intro h
    intro N
    rw [h]

theorem projectiveLimit_prefix_fiber_mem_nhds
    (p : PrefixProjectiveLimit) (N : ℕ) :
    {q : PrefixProjectiveLimit | q.π N = p.π N} ∈ nhds p := by
  exact (projectiveLimit_prefix_fiber_isOpen p N).mem_nhds rfl

theorem projectiveLimit_prefix_fiber_cover (N : ℕ) :
    (⋃ b : BitWord N,
      {q : PrefixProjectiveLimit | q.π N = b}) = Set.univ := by
  ext q
  constructor
  · intro _
    trivial
  · intro _
    exact Set.mem_iUnion.2 ⟨q.π N, rfl⟩

theorem projectiveLimit_prefix_fiber_pairwise_disjoint (N : ℕ) :
    ∀ ⦃b c : BitWord N⦄,
      b ≠ c →
      Disjoint {q : PrefixProjectiveLimit | q.π N = b}
        {q : PrefixProjectiveLimit | q.π N = c} := by
  intro b c hbc
  rw [Set.disjoint_left]
  intro q hqb hqc
  exact hbc (hqb.symm.trans hqc)

/-! ## The Tomita complement lifted to coherent finite prefixes -/

def tomitaProjectiveLimit (p : PrefixProjectiveLimit) : PrefixProjectiveLimit where
  word := fun n i => !(p.word n i)
  coherent := by
    intro n
    funext i
    have h := congrFun (p.coherent n) i
    simpa [prefixSucc] using congrArg (fun b : Bool => !b) h

theorem continuous_tomitaProjectiveLimit :
    Continuous (tomitaProjectiveLimit : PrefixProjectiveLimit → PrefixProjectiveLimit) := by
  rw [continuous_induced_rng]
  change Continuous (fun p : PrefixProjectiveLimit => (tomitaProjectiveLimit p).word)
  change Continuous (fun p : PrefixProjectiveLimit =>
    fun n : ℕ => fun i : Fin n => !(p.word n i))
  exact continuous_pi fun n => continuous_pi fun i =>
    (continuous_of_discreteTopology : Continuous (fun b : Bool => !b)).comp
      ((continuous_apply i).comp (continuous_π n))

@[simp] theorem tomitaProjectiveLimit_involutive
    (p : PrefixProjectiveLimit) :
    tomitaProjectiveLimit (tomitaProjectiveLimit p) = p := by
  apply PrefixProjectiveLimit.ext
  funext n
  funext i
  simp [tomitaProjectiveLimit]

def tomitaProjectiveLimitHomeomorph :
    PrefixProjectiveLimit ≃ₜ PrefixProjectiveLimit :=
  Homeomorph.mk
    { toFun := tomitaProjectiveLimit
      invFun := tomitaProjectiveLimit
      left_inv := tomitaProjectiveLimit_involutive
      right_inv := tomitaProjectiveLimit_involutive }
    continuous_tomitaProjectiveLimit
    continuous_tomitaProjectiveLimit

def tomitaFixedLocus : Set PrefixProjectiveLimit :=
  {p | tomitaProjectiveLimit p = p}

theorem toCantor_tomitaProjectiveLimit
    (p : PrefixProjectiveLimit) :
    toCantor (tomitaProjectiveLimit p) = fun k => !(toCantor p k) := by
  funext k
  rfl

theorem tomitaProjectiveLimit_projection
    (p : PrefixProjectiveLimit) (N : ℕ) :
    π N (tomitaProjectiveLimit p) = fun i => !(π N p i) := by
  rfl

theorem tomitaProjectiveLimit_maps_prefix_fiber
    (p : PrefixProjectiveLimit) (N : ℕ) :
    tomitaProjectiveLimit ''
        {q : PrefixProjectiveLimit | q.π N = p.π N} =
      {q : PrefixProjectiveLimit | q.π N = (tomitaProjectiveLimit p).π N} := by
  ext q
  constructor
  · rintro ⟨r, hr, rfl⟩
    change (tomitaProjectiveLimit r).π N = (tomitaProjectiveLimit p).π N
    rw [tomitaProjectiveLimit_projection, tomitaProjectiveLimit_projection, hr]
  · intro hq
    refine ⟨tomitaProjectiveLimit q, ?_, tomitaProjectiveLimit_involutive q⟩
    change (tomitaProjectiveLimit q).π N = p.π N
    have h := congrArg (fun b : BitWord N => fun i => !(b i)) hq
    simpa [tomitaProjectiveLimit_projection,
      tomitaProjectiveLimit_involutive, tomitaProjectiveLimit] using h

theorem projectiveLimit_tomita_complex_readout_affine
    (p : PrefixProjectiveLimit) :
    binaryReadout (toCantor (tomitaProjectiveLimit p)) +
        binaryReadout (toCantor p) = 1 := by
  rw [toCantor_tomitaProjectiveLimit]
  exact binary_readout_complement (toCantor p)

theorem projectiveLimit_tomita_real_readout_affine
    (p : PrefixProjectiveLimit) :
    realBinaryReadout (toCantor (tomitaProjectiveLimit p)) +
        realBinaryReadout (toCantor p) = 1 := by
  have h := projectiveLimit_tomita_complex_readout_affine p
  rw [complex_binaryReadout_eq_ofReal,
    complex_binaryReadout_eq_ofReal] at h
  exact congrArg Complex.re h

theorem projectiveLimit_tomita_fixed_readout
    (p : PrefixProjectiveLimit)
    (hfixed : tomitaProjectiveLimit p = p) :
    realBinaryReadout (toCantor p) = 1 / 2 := by
  have h := projectiveLimit_tomita_real_readout_affine p
  rw [hfixed] at h
  linarith

theorem projectiveLimit_tomita_fixed_complex_readout
    (p : PrefixProjectiveLimit)
    (hfixed : tomitaProjectiveLimit p = p) :
    binaryReadout (toCantor p) = (1 / 2 : ℂ) := by
  have h := projectiveLimit_tomita_complex_readout_affine p
  rw [hfixed] at h
  linear_combination h / 2

theorem compact_projectiveLimit :
    IsCompact (Set.univ : Set PrefixProjectiveLimit) := by
  have hcompact : IsCompact (Set.univ : Set InfiniteBinaryWordSpace) :=
    isCompact_univ
  have himage := hcompact.image
    PrefixProjectiveLimit.cantorHomeomorphPrefixProjectiveLimit.continuous_toFun
  rw [Set.image_univ] at himage
  change IsCompact (Set.range
    (PrefixProjectiveLimit.cantorHomeomorphPrefixProjectiveLimit :
      InfiniteBinaryWordSpace → PrefixProjectiveLimit)) at himage
  have hrange : Set.range
      (PrefixProjectiveLimit.cantorHomeomorphPrefixProjectiveLimit :
        InfiniteBinaryWordSpace → PrefixProjectiveLimit) = Set.univ :=
    PrefixProjectiveLimit.cantorHomeomorphPrefixProjectiveLimit.surjective.range_eq
  rw [hrange] at himage
  exact himage

theorem compact_projectiveLimit_readout_image :
    IsCompact (Set.range (fun p : PrefixProjectiveLimit =>
      realBinaryReadout (toCantor p))) := by
  simpa only [Set.image_univ] using
    (compact_projectiveLimit).image continuous_projectiveLimit_readout

theorem closed_projectiveLimit_readout_image :
    IsClosed (Set.range (fun p : PrefixProjectiveLimit =>
      realBinaryReadout (toCantor p))) := by
  exact compact_projectiveLimit_readout_image.isClosed

theorem projectiveLimit_prefix_fiber_isCompact
    (p : PrefixProjectiveLimit) (N : ℕ) :
    IsCompact {q : PrefixProjectiveLimit | q.π N = p.π N} := by
  simpa only [Set.univ_inter] using
    compact_projectiveLimit.inter_right
      (projectiveLimit_prefix_fiber_isClosed p N)

theorem projectiveLimit_prefix_fiber_succ_subset
    (p : PrefixProjectiveLimit) (N : ℕ) :
    {q : PrefixProjectiveLimit | q.π (N + 1) = p.π (N + 1)} ⊆
      {q : PrefixProjectiveLimit | q.π N = p.π N} := by
  intro q hq
  change q.π N = p.π N
  rw [← q.projection_coherent N, ← p.projection_coherent N, hq]

theorem projectiveLimit_prefix_fiber_subset_of_le
    (p : PrefixProjectiveLimit) {m n : ℕ} (hmn : m ≤ n) :
    {q : PrefixProjectiveLimit | q.π n = p.π n} ⊆
      {q : PrefixProjectiveLimit | q.π m = p.π m} := by
  induction hmn with
  | refl =>
      intro q hq
      exact hq
  | @step n hmn ih =>
      intro q hq
      exact ih (projectiveLimit_prefix_fiber_succ_subset p n hq)

theorem projectiveLimit_isT2 :
    T2Space PrefixProjectiveLimit := by
  letI := Homeomorph.t2Space
    PrefixProjectiveLimit.cantorHomeomorphPrefixProjectiveLimit
  exact inferInstance

theorem tomitaFixedLocus_isClosed : IsClosed tomitaFixedLocus := by
  letI := projectiveLimit_isT2
  exact isClosed_eq continuous_tomitaProjectiveLimit continuous_id

theorem tomitaFixedLocus_isCompact :
    IsCompact tomitaFixedLocus := by
  exact IsCompact.of_isClosed_subset compact_projectiveLimit
    tomitaFixedLocus_isClosed (by intro p _; exact Set.mem_univ p)

theorem tomitaFixedLocus_eq_empty : tomitaFixedLocus = ∅ := by
  ext p
  constructor
  · intro hp
    have hword : toCantor (tomitaProjectiveLimit p) = toCantor p :=
      congrArg toCantor hp
    have hbit := congrFun hword 0
    simp [toCantor_tomitaProjectiveLimit] at hbit
  · intro hp
    exact False.elim (by simpa using hp)

theorem projectiveLimit_isTotallyDisconnected :
    TotallyDisconnectedSpace PrefixProjectiveLimit := by
  letI := Homeomorph.totallyDisconnectedSpace
    PrefixProjectiveLimit.cantorHomeomorphPrefixProjectiveLimit
  exact inferInstance

/-! ## The binary-expansion ambiguity, exhibited constructively -/

def zeroWord : InfiniteBinaryWordSpace := fun _ => false

def oneWord : InfiniteBinaryWordSpace := fun _ => true

private theorem boundaryPrefix_cons_zeroWord
    (N : ℕ) (b : BitWord N) :
    InfoGeometry.Canonical.FractalCantorCliffordFockBridge.boundaryPrefix N
        (InfoGeometry.Canonical.FractalCantorCliffordFockBridge.boundaryConsList
          (List.ofFn b) zeroWord) = List.ofFn b := by
  induction N with
  | zero => simp [List.ofFn_zero]
  | succ N ih =>
      rw [List.ofFn_succ]
      simp only [InfoGeometry.Canonical.FractalCantorCliffordFockBridge.boundaryConsList,
        InfoGeometry.Canonical.FractalCantorCliffordFockBridge.boundaryPrefix,
        InfoGeometry.Canonical.FractalCantorCliffordFockBridge.boundaryHead,
        InfoGeometry.Canonical.FractalCantorCliffordFockBridge.boundaryTail,
        InfoGeometry.Canonical.FractalCantorCliffordFockBridge.boundaryTail_boundaryCons]
      rw [ih (b := fun i => b i.succ)]
      simp [InfoGeometry.Canonical.FractalCantorCliffordFockBridge.boundaryCons]

theorem realBinaryReadout_zeroWord :
    realBinaryReadout zeroWord = 0 := by
  simp [realBinaryReadout, realBinaryTerm, zeroWord]

theorem zeroTail_extension_readout
    (N : ℕ) (b : BitWord N) :
    realBinaryReadout
        (InfoGeometry.Canonical.FractalCantorCliffordFockBridge.boundaryConsList
          (List.ofFn b) zeroWord) =
      finitePrefixReadout (List.ofFn b) := by
  rw [realBinaryReadout_boundaryConsList]
  rw [realBinaryReadout_zeroWord]
  ring

theorem projectiveLimit_prefix_fiber_nonempty
    (N : ℕ) (b : BitWord N) :
    ∃ p : PrefixProjectiveLimit, p.π N = b := by
  let x : InfiniteBinaryWordSpace :=
    InfoGeometry.Canonical.FractalCantorCliffordFockBridge.boundaryConsList
      (List.ofFn b) zeroWord
  refine ⟨ofCantor x, ?_⟩
  change InfoGeometry.Canonical.UHFInductiveColimitBoundary.boundaryPrefix N x = b
  have hlist := boundaryPrefix_cons_zeroWord N b
  have hbridge :=
    InfoGeometry.Canonical.CantorProjectiveReadoutBridge.bitWordPrefix_list_eq N x
  rw [hlist] at hbridge
  exact List.ofFn_injective hbridge

theorem binaryReadout_zeroWord :
    binaryReadout zeroWord = 0 := by
  simp [binaryReadout, binaryTerm, binaryDigit, zeroWord]

theorem binaryReadout_oneWord :
    binaryReadout oneWord = 1 := by
  have h := binary_readout_complement zeroWord
  simpa [zeroWord, binaryReadout_zeroWord] using h

theorem binaryReadout_boundaryCons_formula
    (a : Bool) (w : InfiniteBinaryWordSpace) :
    binaryReadout (boundaryCons a w) =
      (if a then (1 / 2 : ℂ) else 0) +
        (1 / 2 : ℂ) * binaryReadout w := by
  rw [complex_binaryReadout_eq_ofReal, complex_binaryReadout_eq_ofReal,
    realBinaryReadout_boundaryCons]
  by_cases h : a = true <;> simp [Complex.ofReal_add, Complex.ofReal_mul, h]

theorem binary_expansion_nonunique :
    binaryReadout (boundaryCons true zeroWord) =
      binaryReadout (boundaryCons false oneWord) ∧
    boundaryCons true zeroWord ≠ boundaryCons false oneWord := by
  constructor
  · rw [binaryReadout_boundaryCons_formula, binaryReadout_boundaryCons_formula,
      binaryReadout_zeroWord, binaryReadout_oneWord]
    norm_num
  · intro h
    have h0 := congrFun h 0
    simp [boundaryCons] at h0

/-! ## A finite determinant phase readout -/

def scalarFrame (z : ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  Matrix.diagonal (fun _ : Fin 1 => z)

theorem det_scalarFrame (z : ℂ) :
    (scalarFrame z).det = z := by
  simp [scalarFrame]

def diagonalFrame {n : ℕ} (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal z

theorem det_diagonalFrame {n : ℕ} (z : Fin n → ℂ) :
    (diagonalFrame z).det = ∏ i, z i := by
  exact Matrix.det_diagonal

theorem diagonalFrame_isUnit_iff {n : ℕ} (z : Fin n → ℂ) :
    IsUnit (diagonalFrame z) ↔ ∀ i, z i ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, det_diagonalFrame]
  simp only [isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  simp

theorem scalarFrame_circle_phase_period
    (R : ℝ) (hR : 0 < R) :
    (∮ z in C((0 : ℂ), R), poleForm z) =
      (2 * Real.pi * Complex.I : ℂ) ∧
      (∮ z in C((0 : ℂ), R), poleForm z) /
          (2 * Real.pi * Complex.I) = 1 := by
  constructor
  · exact circleIntegral_one_div R hR
  · rw [circleIntegral_one_div R hR]
    field_simp

end InfoGeometry.Canonical.RindlerMobiusCantorFiniteBridge

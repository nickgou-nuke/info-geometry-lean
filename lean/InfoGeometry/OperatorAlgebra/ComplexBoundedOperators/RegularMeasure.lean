import Mathlib.MeasureTheory.Measure.Regular
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.MetricSpace.Basic

/-!
# AFP regular-measure adapter

This file exposes Lean-native replacements for the elementary reusable parts of
AFP's `Regular_Measure.thy`.

It does not redefine regularity.  Mathlib already provides the proof authority:
`Measure.InnerRegular`, `Measure.OuterRegular`, `Measure.Regular`, and
`Measure.InnerRegularWRT`.
-/

noncomputable section

open scoped ENNReal Topology
open Filter MeasureTheory Set

namespace InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
namespace RegularMeasure

/-! ## Metric neighborhoods -/

section MetricNeighborhoods

variable {α : Type*} [PseudoMetricSpace α]

/-- The metric `r`-neighborhood of a set. -/
def metricNeighborhood (A : Set α) (r : ℝ) : Set α :=
  ⋃ a ∈ A, Metric.ball a r

/--
AFP `nbh_add`: an `f`-neighborhood of the `e`-neighborhood of `A` is contained
in the `(e + f)`-neighborhood of `A`.
-/
theorem nbh_add (A : Set α) (e f : ℝ) :
    (⋃ b ∈ metricNeighborhood A e, Metric.ball b f)
      ⊆ metricNeighborhood A (e + f) := by
  intro x hx
  have hx' :
      ∃ a ∈ A, ∃ b, dist b a < e ∧ dist x b < f := by
    simpa [metricNeighborhood, Metric.mem_ball, exists_and_left, exists_and_right,
      and_assoc] using hx
  rcases hx' with ⟨a, ha, b, hba, hxb⟩
  have hxtri : ∃ a ∈ A, dist x a < e + f := by
    refine ⟨a, ha, ?_⟩
    nlinarith [dist_triangle x b a, hba, hxb]
  simpa [metricNeighborhood, Metric.mem_ball] using hxtri

/-- AFP `nbh_subset`: every set lies in each positive metric neighborhood of itself. -/
theorem subset_nbh (A : Set α) {e : ℝ} (he : 0 < e) :
    A ⊆ metricNeighborhood A e := by
  intro x hx
  simpa [metricNeighborhood, Metric.mem_ball] using
    (show ∃ a ∈ A, dist x a < e from ⟨x, hx, by simpa using he⟩)

/-- AFP `nbh_decseq`: decreasing radii give decreasing metric neighborhoods. -/
theorem nbh_antitone (A : Set α) {r : ℕ → ℝ} (hr : Antitone r) :
    Antitone fun n => metricNeighborhood A (r n) := by
  intro m n hmn x hx
  have hx' : ∃ a ∈ A, dist x a < r n := by
    simpa [metricNeighborhood, Metric.mem_ball] using hx
  rcases hx' with ⟨a, ha, hxa⟩
  have hxa' : dist x a < r m := lt_of_lt_of_le hxa (hr hmn)
  exact by
    simpa [metricNeighborhood, Metric.mem_ball] using
      (show ∃ a ∈ A, dist x a < r m from ⟨a, ha, hxa'⟩)

/--
AFP `nbh_Inter_closure_of`: if positive radii decrease to zero, the intersection
of all metric neighborhoods is the closure.
-/
theorem iInter_nbh_eq_closure (A : Set α) {r : ℕ → ℝ}
    (hrpos : ∀ n, 0 < r n)
    (hrtendsto : Tendsto r atTop (𝓝 0)) :
    (⋂ n, metricNeighborhood A (r n)) = closure A := by
  ext x
  constructor
  · intro hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hIio : Set.Iio ε ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hε
    have hev : ∀ᶠ n : ℕ in atTop, r n ∈ Set.Iio ε :=
      hrtendsto.eventually hIio
    rcases Filter.eventually_atTop.mp hev with ⟨N, hN⟩
    have hxN : x ∈ metricNeighborhood A (r N) := by
      simpa using mem_iInter.mp hx N
    have hxN' : ∃ a ∈ A, dist x a < r N := by
      simpa [metricNeighborhood, Metric.mem_ball] using hxN
    rcases hxN' with ⟨a, ha, hxa⟩
    have hεN : r N < ε := hN N le_rfl
    exact by
      simpa [metricNeighborhood, Metric.mem_ball] using
        (show ∃ a ∈ A, dist x a < ε from ⟨a, ha, lt_trans hxa hεN⟩)
  · intro hx
    rw [mem_iInter]
    intro n
    rw [Metric.mem_closure_iff] at hx
    rcases hx (r n) (hrpos n) with ⟨a, ha, hxa⟩
    exact by
      simpa [metricNeighborhood, Metric.mem_ball] using
        (show ∃ a ∈ A, dist x a < r n from ⟨a, ha, hxa⟩)

end MetricNeighborhoods

/-! ## Countable disjoint measure sums -/

section MeasureSums

variable {α ι : Type*} [MeasurableSpace α] [Countable ι]
variable {μ : Measure α} {s : ι → Set α}

/-- Countable additivity for pairwise-disjoint measurable families. -/
theorem measure_iUnion_eq_tsum
    (hdisj : Pairwise (Function.onFun Disjoint s))
    (hmeas : ∀ i, MeasurableSet (s i)) :
    μ (⋃ i, s i) = ∑' i, μ (s i) :=
  MeasureTheory.measure_iUnion hdisj hmeas

/-- Countable subadditivity. -/
theorem measure_iUnion_le_tsum :
    μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  MeasureTheory.measure_iUnion_le s

end MeasureSums

section FiniteRealMeasureSums

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
variable {s : ℕ → Set α}

/--
AFP `summable_measure`: for a finite measure, the real-valued measures of a
countable disjoint measurable family are summable.
-/
theorem summable_measureReal
    (hmeas : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise (Function.onFun Disjoint s)) :
    Summable fun n => μ.real (s n) :=
  MeasureTheory.summable_measure_toReal hmeas hdisj

/--
AFP `suminf_measure`, real-valued version: for a finite measure, countable
additivity for a disjoint measurable family can be read in `ℝ`.
-/
theorem tsum_measureReal_eq_measureReal_iUnion
    (hmeas : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise (Function.onFun Disjoint s)) :
    (∑' n, μ.real (s n)) = μ.real (⋃ n, s n) := by
  calc
    ∑' n, μ.real (s n) = (∑' n, μ (s n)).toReal := by
      simpa [Measure.real] using (ENNReal.tsum_toReal_eq fun n => measure_ne_top μ (s n)).symm
    _ = μ.real (⋃ n, s n) := by
      simp [Measure.real, MeasureTheory.measure_iUnion hdisj hmeas]

end FiniteRealMeasureSums

/-! ## Mathlib regularity API, exposed under AFP-facing names -/

section Regularity

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
variable {μ : Measure α} {A U : Set α}

/--
Mathlib's inner-regularity readout: measurable sets are approximated from
inside by compact sets.
-/
theorem innerRegular_measure_eq_iSup_isCompact
    [Measure.InnerRegular μ]
    (hA : MeasurableSet A) :
    μ A = ⨆ (K : Set α) (_ : K ⊆ A) (_ : IsCompact K), μ K :=
  hA.measure_eq_iSup_isCompact μ

/--
Mathlib's outer-regularity readout: arbitrary sets are approximated from
outside by open sets.
-/
theorem outerRegular_measure_eq_iInf_isOpen
    [Measure.OuterRegular μ] :
    μ A = ⨅ (V : Set α) (_ : A ⊆ V) (_ : IsOpen V), μ V :=
  A.measure_eq_iInf_isOpen μ

/--
A regular measure is inner regular on open sets using compact subsets.
This is the direct mathlib analogue of the open-set part of AFP regularity.
-/
theorem regular_open_measure_eq_iSup_isCompact
    [Measure.Regular μ]
    (hU : IsOpen U) :
    μ U = ⨆ (K : Set α) (_ : K ⊆ U) (_ : IsCompact K), μ K :=
  Measure.Regular.innerRegular.measure_eq_iSup hU

/--
Inner regularity for finite-measure sets with compact approximants.
-/
theorem innerRegularCompactLTTop_measure_eq_iSup_isCompact_of_ne_top
    [Measure.InnerRegularCompactLTTop μ]
    (hA : MeasurableSet A)
    (hAfin : μ A ≠ ∞) :
    μ A = ⨆ (K : Set α) (_ : K ⊆ A) (_ : IsCompact K), μ K :=
  hA.measure_eq_iSup_isCompact_of_ne_top hAfin

/-- Approximation from inside by a compact subset with measure within `ε`. -/
theorem exists_isCompact_lt_add_of_innerRegularCompactLTTop
    [Measure.InnerRegularCompactLTTop μ]
    (hA : MeasurableSet A)
    (hAfin : μ A ≠ ∞)
    {ε : ℝ≥0∞}
    (hε : ε ≠ 0) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧ μ A < μ K + ε :=
  hA.exists_isCompact_lt_add hAfin hε

/-- Outer approximation by an open superset with measure within `ε`. -/
theorem exists_isOpen_lt_add_of_outerRegular
    [Measure.OuterRegular μ]
    (hAfin : μ A ≠ ∞)
    {ε : ℝ≥0∞}
    (hε : ε ≠ 0) :
    ∃ V, A ⊆ V ∧ IsOpen V ∧ μ V < μ A + ε :=
  A.exists_isOpen_lt_add hAfin hε

end Regularity

section MetrizableRegularity

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
variable {μ : Measure α}

/--
In a pseudometrizable space, open sets are inner-regular with respect to closed
subsets. This is mathlib's direct replacement for the closed-set part of AFP's
finite metrizable regularity argument.
-/
theorem innerRegularWRT_isClosed_isOpen_of_pseudoMetrizable
    [TopologicalSpace.PseudoMetrizableSpace α] :
    μ.InnerRegularWRT IsClosed IsOpen :=
  MeasureTheory.Measure.InnerRegularWRT.of_pseudoMetrizableSpace μ

/--
In a sigma-compact space, closed sets are inner-regular with respect to compact
subsets.
-/
theorem innerRegularWRT_isCompact_isClosed_of_sigmaCompact
    [SigmaCompactSpace α] :
    μ.InnerRegularWRT IsCompact IsClosed :=
  MeasureTheory.Measure.InnerRegularWRT.isCompact_isClosed μ

/--
Finite measures on complete second-countable pseudometrizable Borel spaces are
inner regular with compact closed approximants.
-/
theorem innerRegularWRT_isCompact_isClosed_measurableSet_of_finite
    [SecondCountableTopology α]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace α]
    [BorelSpace α]
    [IsFiniteMeasure μ] :
    μ.InnerRegularWRT (fun K => IsCompact K ∧ IsClosed K) MeasurableSet :=
  MeasureTheory.innerRegular_isCompact_isClosed_measurableSet_of_finite μ

/--
Finite measures on complete second-countable pseudometrizable Borel spaces are
mathlib-inner-regular.
-/
theorem innerRegular_of_completeSecondCountablePseudoMetrizable
    [SecondCountableTopology α]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace α]
    [BorelSpace α]
    [IsFiniteMeasure μ] :
    μ.InnerRegular :=
  inferInstance

/--
Finite measures with compact-finite inner regularity in an R₁ Borel space are
regular in mathlib's sense.
-/
theorem regular_of_innerRegularCompactLTTop_finite
    [BorelSpace α]
    [R1Space α]
    [Measure.InnerRegularCompactLTTop μ]
    [IsFiniteMeasure μ] :
    μ.Regular :=
  inferInstance

end MetrizableRegularity

/-! ## Tightness API -/

section Tightness

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
variable {μ : Measure α} {S T : Set (Measure α)}

/--
Mathlib's tightness definition unfolded into the AFP-facing compact-complement
form.
-/
theorem isTightMeasureSet_iff_exists_isCompact_measure_compl_le :
    IsTightMeasureSet S ↔
      ∀ ε, 0 < ε → ∃ K : Set α, IsCompact K ∧ ∀ μ ∈ S, μ (Kᶜ) ≤ ε :=
  MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le

/-- AFP `tight_on_set_subset`, expressed through mathlib `IsTightMeasureSet`. -/
theorem tightMeasureSet_subset
    (hT : IsTightMeasureSet T)
    (hST : S ⊆ T) :
    IsTightMeasureSet S :=
  hT.subset hST

/-- In a compact space, every family of measures is tight. -/
theorem tightMeasureSet_of_compactSpace [CompactSpace α] :
    IsTightMeasureSet S :=
  IsTightMeasureSet.of_compactSpace

/-- A finite inner-regular measure on a T₂ measurable topological space is tight. -/
theorem tightSingleton_of_innerRegular
    [T2Space α] [OpensMeasurableSpace α] [IsFiniteMeasure μ]
    [μ.InnerRegular] :
    IsTightMeasureSet {μ} :=
  MeasureTheory.isTightMeasureSet_singleton_of_innerRegular

/-- Complete second-countable pseudometrizable spaces have tight finite measures. -/
theorem tightSingleton_of_completeSecondCountablePseudoMetric
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace α]
    [SecondCountableTopology α]
    [BorelSpace α]
    [IsFiniteMeasure μ] :
    IsTightMeasureSet {μ} :=
  MeasureTheory.isTightMeasureSet_singleton

end Tightness

end RegularMeasure
end InfoGeometry.OperatorAlgebra.ComplexBoundedOperators

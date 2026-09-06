import InfoGeometry.Canonical.CantorBoundaryReadoutKernelQuotientTopCat
import InfoGeometry.Canonical.CantorBoundaryDyadicCover
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Interval-valued target for the binary readout quotient

The kernel quotient has a continuous readout into `ℝ` whose values lie in
`Set.Icc (0 : ℝ) 1`.  This file records the resulting subtype-valued map and
isolates the remaining target-identification obligation as an explicit
surjectivity property.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryReadoutIntervalTarget

open CategoryTheory
open InfoGeometry.Canonical.CantorBoundaryReadoutKernelQuotientTopCat
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryDyadicCover

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

local instance unitIntervalT2 : T2Space UnitInterval :=
  TopologicalSpace.t2Space_of_metrizableSpace

def quotientReadoutInterval (q : ReadoutQuotient) : UnitInterval :=
  ⟨quotientReadout q, quotientReadout_mem_unitInterval q⟩

theorem continuous_quotientReadoutInterval :
    Continuous quotientReadoutInterval := by
  exact quotientReadout_continuous.subtype_mk (fun q =>
    quotientReadout_mem_unitInterval q)

theorem quotientReadoutInterval_injective :
    Function.Injective quotientReadoutInterval := by
  intro q₁ q₂ h
  apply quotientReadout_injective
  exact congrArg Subtype.val h

theorem isCompact_quotientReadoutInterval_range :
    IsCompact (Set.range quotientReadoutInterval) := by
  have h_image :=
    quotient_compact.image continuous_quotientReadoutInterval
  simpa only [Set.image_univ] using h_image

theorem isClosed_quotientReadoutInterval_range :
    IsClosed (Set.range quotientReadoutInterval) := by
  exact isCompact_quotientReadoutInterval_range.isClosed

theorem quotientReadoutInterval_isClosedEmbedding :
    Topology.IsClosedEmbedding quotientReadoutInterval := by
  letI : CompactSpace ReadoutQuotient :=
    ⟨by simpa using quotient_compact⟩
  exact continuous_quotientReadoutInterval.isClosedEmbedding
    quotientReadoutInterval_injective

theorem quotientReadoutInterval_surjective_of_metric_approximation
    (happrox : ∀ y : UnitInterval, ∀ ε : ℝ, 0 < ε →
      ∃ q : ReadoutQuotient,
        dist y (quotientReadoutInterval q) < ε) :
    Function.Surjective quotientReadoutInterval := by
  intro y
  have hy_closure : y ∈ closure (Set.range quotientReadoutInterval) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q, hq⟩ := happrox y ε hε
    exact ⟨quotientReadoutInterval q, ⟨q, rfl⟩, hq⟩
  have hy_range : y ∈ Set.range quotientReadoutInterval := by
    have hsubset :
        closure (Set.range quotientReadoutInterval) ⊆
          Set.range quotientReadoutInterval :=
      isClosed_quotientReadoutInterval_range.closure_subset_iff.mpr
        (by intro z hz; exact hz)
    exact hsubset hy_closure
  exact hy_range

theorem quotientReadoutInterval_metric_approximation :
    ∀ y : UnitInterval, ∀ ε : ℝ, 0 < ε →
      ∃ q : ReadoutQuotient,
        dist y (quotientReadoutInterval q) < ε := by
  intro y ε hε
  obtain ⟨w, hw⟩ := exists_realBinaryReadout_close y.1 y.2 hε
  refine ⟨quotientMap w, ?_⟩
  change dist (y : ℝ) (realBinaryReadout w) < ε
  simpa [Real.dist_eq] using hw

theorem quotientReadoutInterval_surjective :
    Function.Surjective quotientReadoutInterval := by
  exact quotientReadoutInterval_surjective_of_metric_approximation
    quotientReadoutInterval_metric_approximation

theorem quotientReadoutInterval_range_eq_univ :
    Set.range quotientReadoutInterval = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact quotientReadoutInterval_surjective x

noncomputable def quotientReadoutIntervalEquiv
    (h_surjective : Function.Surjective quotientReadoutInterval) :
    ReadoutQuotient ≃ UnitInterval :=
  Equiv.ofBijective quotientReadoutInterval
    ⟨quotientReadoutInterval_injective, h_surjective⟩

theorem quotientReadoutIntervalEquiv_apply
    (h_surjective : Function.Surjective quotientReadoutInterval)
    (q : ReadoutQuotient) :
    quotientReadoutIntervalEquiv h_surjective q = quotientReadoutInterval q :=
  rfl

noncomputable def quotientReadoutIntervalHomeomorph
    (happrox : ∀ y : UnitInterval, ∀ ε : ℝ, 0 < ε →
      ∃ q : ReadoutQuotient,
        dist y (quotientReadoutInterval q) < ε) :
    ReadoutQuotient ≃ₜ UnitInterval := by
  letI : CompactSpace ReadoutQuotient :=
    ⟨by simpa using quotient_compact⟩
  let e : ReadoutQuotient ≃ UnitInterval :=
    quotientReadoutIntervalEquiv
      (quotientReadoutInterval_surjective_of_metric_approximation happrox)
  have he : Continuous e := by
    simpa [e] using continuous_quotientReadoutInterval
  exact Continuous.homeoOfEquivCompactToT2 he

theorem quotientReadoutIntervalHomeomorph_apply
    (happrox : ∀ y : UnitInterval, ∀ ε : ℝ, 0 < ε →
      ∃ q : ReadoutQuotient,
        dist y (quotientReadoutInterval q) < ε)
    (q : ReadoutQuotient) :
    quotientReadoutIntervalHomeomorph happrox q =
      quotientReadoutInterval q := by
  change
    quotientReadoutIntervalEquiv
        (quotientReadoutInterval_surjective_of_metric_approximation happrox) q =
      quotientReadoutInterval q
  rfl

noncomputable def canonicalQuotientReadoutIntervalHomeomorph :
    ReadoutQuotient ≃ₜ UnitInterval :=
  quotientReadoutIntervalHomeomorph quotientReadoutInterval_metric_approximation

theorem canonicalQuotientReadoutIntervalHomeomorph_apply
    (q : ReadoutQuotient) :
    canonicalQuotientReadoutIntervalHomeomorph q =
      quotientReadoutInterval q := by
  exact quotientReadoutIntervalHomeomorph_apply
    quotientReadoutInterval_metric_approximation q

noncomputable def canonicalQuotientReadoutIntervalSourceCompHaus : CompHaus := by
  letI : CompactSpace ReadoutQuotient :=
    ⟨by simpa using quotient_compact⟩
  let e := canonicalQuotientReadoutIntervalHomeomorph
  letI : T2Space ReadoutQuotient := e.symm.t2Space
  exact CompHaus.of ReadoutQuotient

noncomputable def canonicalQuotientReadoutIntervalCompHausIso :
    canonicalQuotientReadoutIntervalSourceCompHaus ≅ CompHaus.of UnitInterval := by
  letI : CompactSpace ReadoutQuotient :=
    ⟨by simpa using quotient_compact⟩
  let e := canonicalQuotientReadoutIntervalHomeomorph
  letI : T2Space ReadoutQuotient := e.symm.t2Space
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := e
          continuous_toFun := e.continuous_toFun }⟩
      inv := ⟨TopCat.ofHom
        { toFun := e.symm
          continuous_toFun := e.symm.continuous_toFun }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro q
        change e.symm (e q) = q
        exact e.symm_apply_apply q
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e (e.symm y) = y
        exact e.apply_symm_apply y }

theorem canonicalQuotientReadoutIntervalCompHausIso_hom_apply
    (q : ReadoutQuotient) :
    (canonicalQuotientReadoutIntervalCompHausIso).hom q =
      canonicalQuotientReadoutIntervalHomeomorph q :=
  rfl

theorem quotientReadoutInterval_isQuotientMap :
    Topology.IsQuotientMap quotientReadoutInterval := by
  letI : CompactSpace ReadoutQuotient :=
    ⟨by simpa using quotient_compact⟩
  exact InfoGeometry.Topology.NaryTreeBoundaryQuotientTopCat.isQuotientMap_of_compactSpace_of_t2
    quotientReadoutInterval
    (quotientReadoutInterval_surjective_of_metric_approximation
      quotientReadoutInterval_metric_approximation)
    continuous_quotientReadoutInterval

theorem continuous_canonicalQuotientReadoutInterval_pullback
    {Y : Type*} [TopologicalSpace Y]
    (f : UnitInterval → Y) (hf : Continuous f) :
    Continuous
      (f ∘ canonicalQuotientReadoutIntervalHomeomorph) := by
  exact hf.comp canonicalQuotientReadoutIntervalHomeomorph.continuous

theorem canonicalQuotientReadoutInterval_pullback_comp_quotientMap
    {Y : Type*} [TopologicalSpace Y]
    (f : UnitInterval → Y) :
    (f ∘ canonicalQuotientReadoutIntervalHomeomorph) ∘ quotientMap =
      f ∘ quotientReadoutInterval ∘ quotientMap := by
  funext w
  simp only [Function.comp_apply,
    canonicalQuotientReadoutIntervalHomeomorph_apply]

end InfoGeometry.Canonical.CantorBoundaryReadoutIntervalTarget

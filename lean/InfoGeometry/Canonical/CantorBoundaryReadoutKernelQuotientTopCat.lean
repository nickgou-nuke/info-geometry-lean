import InfoGeometry.Canonical.CantorBoundaryReadoutTopCat
import InfoGeometry.Canonical.CantorBoundaryReadoutIntervalApproximation
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
import InfoGeometry.Topology.NaryTreeBoundaryQuotientTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Kernel quotient of the binary Cantor readout

The binary series readout has a canonical quotient by equality of readout
values.  This owner records the resulting `TopCat` map and its injectivity.
It does not identify the quotient with the unit interval: that requires a
separate surjectivity and topology theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryReadoutKernelQuotientTopCat

open CategoryTheory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorBoundaryReadoutIntervalApproximation
open InfoGeometry.Topology.NaryTreeBoundaryQuotientTopCat

local instance : T2Space ℝ := TopologicalSpace.t2Space_of_metrizableSpace

def readoutSetoid : Setoid (ℕ → Bool) where
  r x y := realBinaryReadout x = realBinaryReadout y
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

abbrev ReadoutQuotient := BoundaryQuotient (A := Bool) readoutSetoid

def quotientMap : (ℕ → Bool) → ReadoutQuotient :=
  boundaryQuotientMap (A := Bool) readoutSetoid

def quotientReadout : ReadoutQuotient → ℝ :=
  InfoGeometry.Topology.NaryTreeBoundaryQuotientTopCat.quotientReadout
    (A := Bool) readoutSetoid realBinaryReadout (by
      intro x y h
      exact h)

theorem quotientMap_continuous : Continuous quotientMap := by
  exact continuous_boundaryQuotientMap (A := Bool) readoutSetoid

theorem quotientMap_isQuotientMap :
    Topology.IsQuotientMap quotientMap := by
  exact isQuotientMap_boundaryQuotientMap (A := Bool) readoutSetoid

theorem quotientMap_surjective : Function.Surjective quotientMap := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact ⟨x, rfl⟩

theorem quotientReadout_continuous : Continuous quotientReadout := by
  exact InfoGeometry.Topology.NaryTreeBoundaryQuotientTopCat.continuous_quotientReadout
    (A := Bool) readoutSetoid realBinaryReadout
    continuous_realBinaryReadout (by
      intro x y h
      exact h)

@[simp] theorem quotientReadout_comp (x : (ℕ → Bool)) :
    quotientReadout (quotientMap x) = realBinaryReadout x := by
  exact InfoGeometry.Topology.NaryTreeBoundaryQuotientTopCat.quotientReadout_mk
    (A := Bool) readoutSetoid realBinaryReadout (by
      intro x y h
      exact h) x

theorem quotientMap_eq_iff (x y : (ℕ → Bool)) :
    quotientMap x = quotientMap y ↔
      realBinaryReadout x = realBinaryReadout y := by
  constructor
  · intro h
    simpa using congrArg quotientReadout h
  · intro h
    exact Quotient.sound h

theorem quotientReadout_injective :
    Function.Injective quotientReadout := by
  intro q₁
  refine Quotient.inductionOn q₁ ?_
  intro x q₂
  refine Quotient.inductionOn q₂ ?_
  intro y h
  have hxy : realBinaryReadout x = realBinaryReadout y := by
    simpa [quotientReadout] using h
  apply Quotient.sound
  exact hxy

theorem quotientReadout_eq_iff (q₁ q₂ : ReadoutQuotient) :
    quotientReadout q₁ = quotientReadout q₂ ↔ q₁ = q₂ := by
  constructor
  · intro h
    exact quotientReadout_injective h
  · intro h
    exact congrArg quotientReadout h

theorem quotientReadout_mem_unitInterval (q : ReadoutQuotient) :
    quotientReadout q ∈ Set.Icc (0 : ℝ) 1 := by
  refine Quotient.inductionOn q ?_
  intro x
  simpa [quotientReadout] using
    (realBinaryReadout_mem_unitInterval x)

theorem quotientReadout_range_eq_unitInterval :
    Set.range quotientReadout = Set.Icc (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact quotientReadout_mem_unitInterval q
  · intro hx
    obtain ⟨w, hw⟩ := intervalReadout_surjective ⟨x, hx⟩
    refine ⟨quotientMap w, ?_⟩
    simpa [intervalReadout] using hw

theorem quotient_compact :
    IsCompact (Set.univ : Set ReadoutQuotient) := by
  have himage : IsCompact (Set.range quotientMap) := by
    have hsource : IsCompact (Set.univ : Set (ℕ → Bool)) := cantorBoundary_compact
    simpa using hsource.image quotientMap_continuous
  rw [Set.range_eq_univ.2 quotientMap_surjective] at himage
  exact himage

noncomputable def quotientReadoutTopCatHom :
    TopCat.of ReadoutQuotient ⟶ TopCat.of ℝ :=
  InfoGeometry.Topology.NaryTreeBoundaryQuotientTopCat.quotientReadoutTopCatHom
    (A := Bool) readoutSetoid realBinaryReadout
    continuous_realBinaryReadout (by
      intro x y h
      exact h)

noncomputable def quotientReadoutRangeHomeomorph :
    ReadoutQuotient ≃ₜ Set.range quotientReadout := by
  letI : CompactSpace ReadoutQuotient := ⟨quotient_compact⟩
  exact (quotientReadout_continuous.isClosedEmbedding quotientReadout_injective).isEmbedding.toHomeomorph

noncomputable def quotientReadoutUnitIntervalHomeomorph :
    ReadoutQuotient ≃ₜ Set.Icc (0 : ℝ) 1 :=
  quotientReadoutRangeHomeomorph.trans
    (Homeomorph.setCongr quotientReadout_range_eq_unitInterval)

@[simp] theorem quotientReadoutUnitIntervalHomeomorph_apply
    (q : ReadoutQuotient) :
    quotientReadoutUnitIntervalHomeomorph q =
      ⟨quotientReadout q, quotientReadout_mem_unitInterval q⟩ :=
  rfl

noncomputable def quotientReadoutCompHaus : CompHaus := by
  letI : CompactSpace (Set.range quotientReadout) :=
    isCompact_iff_compactSpace.mp (by
      simpa using quotient_compact.image quotientReadout_continuous)
  exact CompHaus.of (Set.range quotientReadout)

noncomputable def quotientReadoutSourceCompHaus : CompHaus := by
  letI : CompactSpace ReadoutQuotient := ⟨quotient_compact⟩
  letI : T2Space (Set.range quotientReadout) := inferInstance
  letI : T2Space ReadoutQuotient :=
    (quotientReadoutRangeHomeomorph).symm.t2Space
  exact CompHaus.of ReadoutQuotient

noncomputable def quotientReadoutCompHausIso :
    quotientReadoutSourceCompHaus ≅ quotientReadoutCompHaus := by
  letI : CompactSpace ReadoutQuotient := ⟨quotient_compact⟩
  letI : T2Space (Set.range quotientReadout) := inferInstance
  letI : T2Space ReadoutQuotient :=
    (quotientReadoutRangeHomeomorph).symm.t2Space
  letI : CompactSpace (Set.range quotientReadout) :=
    isCompact_iff_compactSpace.mp (by
      simpa using quotient_compact.image quotientReadout_continuous)
  let e := quotientReadoutRangeHomeomorph
  change CompHaus.of ReadoutQuotient ≅ CompHaus.of (Set.range quotientReadout)
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

theorem quotientReadoutCompHausIso_hom_apply
    (q : ReadoutQuotient) :
    (quotientReadoutCompHausIso).hom q = quotientReadoutRangeHomeomorph q :=
  rfl

end InfoGeometry.Canonical.CantorBoundaryReadoutKernelQuotientTopCat

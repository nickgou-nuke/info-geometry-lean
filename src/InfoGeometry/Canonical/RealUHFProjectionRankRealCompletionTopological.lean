import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFProjectionRankIntervalTopological

/-!
# Real completion target for dyadic normalized rank readouts

The dyadic readout embeds into the real unit interval.  The target interval is
compact; the dyadic image is not asserted to be surjective or compact.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological

open InfoGeometry.Canonical
open InfoGeometry.Canonical.RealUHFProjectionRankIntervalTopological

abbrev RealUnitInterval := Set.Icc (0 : ℝ) 1

def dyadicToRealInterval (q : DyadicUnitInterval) : RealUnitInterval :=
  ⟨((q : ℚ) : ℝ), by
    exact ⟨(Rat.cast_nonneg).2 q.property.1,
      by simpa using (Rat.cast_le).2 q.property.2⟩⟩

theorem continuous_dyadicToRealInterval :
    Continuous dyadicToRealInterval := by
  apply Continuous.subtype_mk
  · exact (continuous_induced_dom :
      Continuous (fun q : ℚ => (q : ℝ))).comp continuous_subtype_val

theorem dyadicToRealInterval_injective :
    Function.Injective dyadicToRealInterval := by
  intro q r h
  apply Subtype.ext
  exact Rat.cast_injective (α := ℝ) (congrArg Subtype.val h)

theorem isCompact_univ_realUnitInterval :
    IsCompact (Set.univ : Set RealUnitInterval) := by
  letI : CompactSpace RealUnitInterval :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  exact isCompact_univ

def compatibleToRealInterval
    (f : CompatibleIntervalReadout) : RealUnitInterval :=
  dyadicToRealInterval (f.1 0)

theorem continuous_compatibleToRealInterval :
    Continuous compatibleToRealInterval := by
  exact continuous_dyadicToRealInterval.comp
    (continuous_intervalReadout_coordinate 0)

def compatibleToRealIntervalTopCatHom :
    TopCat.of CompatibleIntervalReadout ⟶ TopCat.of RealUnitInterval :=
  TopCat.ofHom
    { toFun := compatibleToRealInterval
      continuous_toFun := continuous_compatibleToRealInterval }

@[simp] theorem compatibleToRealIntervalTopCatHom_apply
    (f : CompatibleIntervalReadout) :
    compatibleToRealIntervalTopCatHom f =
      compatibleToRealInterval f := rfl

theorem dyadicToRealInterval_coordinate_eq_compatible
    (f : CompatibleIntervalReadout) (n : ℕ) :
    dyadicToRealInterval (f.1 n) =
      compatibleToRealInterval f := by
  have h : f.1 n = f.1 0 := by
    induction n with
    | zero => rfl
    | succ n ih => exact (f.2 n).trans ih
  exact congrArg dyadicToRealInterval h

theorem compatibleToRealInterval_normalized
    (S : RealUHFProjectionRankSystem) :
    compatibleToRealInterval (normalizedIntervalReadout S) =
      dyadicToRealInterval (S.normalizedReadoutInterval 0) := rfl

end InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological

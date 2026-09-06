import Mathlib
import InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological

/-!
# The real completion square for compatible projection-rank readouts

This owner records the continuous comparison map from the dyadic interval
readout to the real unit interval.  It proves that every compatible stage
coordinate has the same real image.  It does not identify this readout with a
state space, a KMS simplex, or a completed UHF algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFProjectionRankCompletionReadoutSquare

open CategoryTheory
open InfoGeometry.Canonical
open InfoGeometry.Canonical.RealUHFProjectionRankIntervalTopological
open InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological

def dyadicToRealIntervalTopCatHom :
    TopCat.of DyadicUnitInterval ⟶ TopCat.of RealUnitInterval :=
  TopCat.ofHom
    { toFun := dyadicToRealInterval
      continuous_toFun := continuous_dyadicToRealInterval }

@[simp] theorem dyadicToRealIntervalTopCatHom_apply
    (q : DyadicUnitInterval) :
    dyadicToRealIntervalTopCatHom q = dyadicToRealInterval q := rfl

theorem coordinate_completion_square (n : ℕ) :
    coordinateTopCatHom n ≫ dyadicToRealIntervalTopCatHom =
      compatibleToRealIntervalTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro f
  rw [TopCat.comp_app]
  change dyadicToRealInterval (f.1 n) =
    compatibleToRealInterval f
  exact dyadicToRealInterval_coordinate_eq_compatible f n

theorem normalized_coordinate_completion_square
    (S : RealUHFProjectionRankSystem) (n : ℕ) :
    dyadicToRealIntervalTopCatHom
        (coordinateTopCatHom n (normalizedIntervalReadout S)) =
      compatibleToRealIntervalTopCatHom (normalizedIntervalReadout S) := by
  change dyadicToRealInterval
      ((normalizedIntervalReadout S).1 n) =
    compatibleToRealInterval (normalizedIntervalReadout S)
  exact dyadicToRealInterval_coordinate_eq_compatible
    (normalizedIntervalReadout S) n

noncomputable def normalizedRealReadout
    (S : RealUHFProjectionRankSystem) : RealUnitInterval :=
  compatibleToRealInterval (normalizedIntervalReadout S)

theorem normalizedRealReadout_eq_stage
    (S : RealUHFProjectionRankSystem) (n : ℕ) :
    dyadicToRealInterval (S.normalizedReadoutInterval n) =
      normalizedRealReadout S := by
  change dyadicToRealInterval
      ((normalizedIntervalReadout S).1 n) =
    compatibleToRealInterval (normalizedIntervalReadout S)
  exact dyadicToRealInterval_coordinate_eq_compatible
    (normalizedIntervalReadout S) n

end RealUHFProjectionRankCompletionReadoutSquare

end Canonical

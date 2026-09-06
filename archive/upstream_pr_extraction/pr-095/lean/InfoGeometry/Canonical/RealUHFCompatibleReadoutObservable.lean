import InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirror
import InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological

/-!
# Observable bridge from continuous readout families to the dyadic interval

The continuous-family carrier and the projection-rank carrier are different
types.  This owner connects them only through explicit interval-readout data.
It deliberately does not infer a projection system, rank preservation, or a
canonical observable from a mirror.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutObservable

open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFProjectionRankIntervalTopological
open InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological

abbrev carrier := CompatibleContinuousReadoutFamily

structure Data where
  intervalReadout : carrier → CompatibleIntervalReadout
  continuous_intervalReadout : Continuous intervalReadout

def realObservable (D : Data) (ρ : carrier) : RealUnitInterval :=
  compatibleToRealInterval (D.intervalReadout ρ)

theorem continuous_realObservable (D : Data) :
    Continuous (realObservable D) := by
  exact continuous_compatibleToRealInterval.comp D.continuous_intervalReadout

noncomputable def realObservableTopCatHom (D : Data) :
    TopCat.of carrier ⟶ TopCat.of RealUnitInterval :=
  TopCat.ofHom
    { toFun := realObservable D
      continuous_toFun := continuous_realObservable D }

@[simp] theorem realObservableTopCatHom_apply
    (D : Data) (ρ : carrier) :
    realObservableTopCatHom D ρ = realObservable D ρ :=
  rfl

structure MirrorData
    (M : InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirror.Data)
    extends Data where
  preserves_intervalReadout : ∀ ρ : carrier,
    intervalReadout (InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirror.involution M ρ) =
      intervalReadout ρ

theorem mirror_preserves_realObservable
    (M : InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirror.Data)
    (D : MirrorData M) (ρ : carrier) :
    realObservable D.toData
        (InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirror.involution M ρ) =
      realObservable D.toData ρ := by
  unfold realObservable
  rw [D.preserves_intervalReadout]

end InfoGeometry.Canonical.RealUHFCompatibleReadoutObservable
end

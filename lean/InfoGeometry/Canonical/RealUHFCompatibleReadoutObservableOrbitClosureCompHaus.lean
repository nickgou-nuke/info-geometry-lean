import InfoGeometry.Canonical.RealUHFCompatibleReadoutObservableFlowCompHaus
import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitReversal

/-!
# Orbit-closure `CompHaus` observables

The ambient observable is restricted to the existing compact orbit-closure
carrier.  No new closure or compactification is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutObservableOrbitClosureCompHaus

open CategoryTheory
open InfoGeometry.Canonical.RealUHFCompatibleReadoutObservable
open InfoGeometry.Canonical.RealUHFCompatibleReadoutObservableFlow
open InfoGeometry.Canonical.RealUHFCompatibleReadoutObservableFlowCompHaus
open InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirror
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitOrbitClosureCompHaus
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitOrbitClosureFlowCompHaus
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitReversal
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitSymbolicLatentFlow
open InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological

abbrev carrier := CompatibleContinuousReadoutFamily
abbrev flow := scalarDilationCompatibleReadoutFamilyFlow

variable [CompactSpace carrier] [T2Space carrier]

noncomputable def orbitObservableCompHausHom
    (D : RealUHFCompatibleReadoutObservable.Data)
    (ρ : carrier) :
    orbitClosureCompHaus ρ ⟶ CompHaus.of RealUnitInterval :=
  orbitClosureInclusionCompHausHom ρ ≫ observableCompHausHom D

theorem orbitObservableCompHausHom_apply
    (D : RealUHFCompatibleReadoutObservable.Data)
    (ρ : carrier) (y : orbitClosureCompHaus ρ) :
    orbitObservableCompHausHom D ρ y = realObservable D y.1 :=
  rfl

theorem orbitObservable_flow_square
    (D : FlowData) (ρ : carrier) (t : ℝ) :
    (orbitClosureFlowCompHausIso ρ t).hom ≫
        orbitObservableCompHausHom D.observable (flow.act t ρ) =
      orbitObservableCompHausHom D.observable ρ := by
  apply ConcreteCategory.hom_ext
  intro y
  change realObservable D.observable (flow.act t y.1) =
    realObservable D.observable y.1
  exact D.invariant t y.1

theorem orbitObservable_mirror_square
    (D : ReversalData) (ρ : carrier) :
    ((reversalData (involution D.mirror) D.reverses_flow).orbitClosureCompHausIso ρ).hom ≫
        orbitObservableCompHausHom D.observable.toData
          (involution D.mirror ρ) =
      orbitObservableCompHausHom D.observable.toData ρ := by
  apply ConcreteCategory.hom_ext
  intro y
  change realObservable D.observable.toData (involution D.mirror y.1) =
    realObservable D.observable.toData y.1
  exact mirror_preserves D y.1

end InfoGeometry.Canonical.RealUHFCompatibleReadoutObservableOrbitClosureCompHaus
end

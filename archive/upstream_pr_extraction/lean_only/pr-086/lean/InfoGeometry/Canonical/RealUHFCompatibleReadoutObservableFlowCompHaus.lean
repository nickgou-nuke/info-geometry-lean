import InfoGeometry.Canonical.RealUHFCompatibleReadoutObservableFlow
import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitReversalTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# `CompHaus` commutative squares for compatible-family observables

The carrier is used only under explicit `CompactSpace` and `T2Space`
assumptions.  The squares are pointwise consequences of the conservation and
reversal fields of the preceding owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutObservableFlowCompHaus

open CategoryTheory
open InfoGeometry.Canonical.RealUHFCompatibleReadoutObservable
open InfoGeometry.Canonical.RealUHFCompatibleReadoutObservableFlow
open InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirror
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitSymbolicLatentFlow
open InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitReversalTopCat
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitOrbitClosureCompHaus

abbrev carrier := CompatibleContinuousReadoutFamily
abbrev flow := scalarDilationCompatibleReadoutFamilyFlow

variable [CompactSpace carrier] [T2Space carrier]

noncomputable def flowCompHausHom (t : ℝ) :
    CompHaus.of carrier ⟶ CompHaus.of carrier :=
  ⟨flow.actTopCatHom t⟩

noncomputable def observableCompHausHom
    (D : RealUHFCompatibleReadoutObservable.Data) :
    CompHaus.of carrier ⟶ CompHaus.of RealUnitInterval :=
  ⟨realObservableTopCatHom D⟩

noncomputable def mirrorCompHausHom
    (M : RealUHFCompatibleReadoutFamilyMirror.Data) :
    CompHaus.of carrier ⟶ CompHaus.of carrier :=
  ⟨(involution M).toTopCatHom⟩

theorem flow_observable_square (D : FlowData) (t : ℝ) :
    flowCompHausHom t ≫ observableCompHausHom D.observable =
      observableCompHausHom D.observable := by
  apply ConcreteCategory.hom_ext
  intro ρ
  change realObservable D.observable (flow.act t ρ) =
    realObservable D.observable ρ
  exact D.invariant t ρ

theorem mirror_observable_square (D : ReversalData) :
    mirrorCompHausHom D.mirror ≫
        observableCompHausHom D.observable.toData =
      observableCompHausHom D.observable.toData := by
  apply ConcreteCategory.hom_ext
  intro ρ
  change realObservable D.observable.toData (involution D.mirror ρ) =
    realObservable D.observable.toData ρ
  exact mirror_preserves D ρ

theorem mirror_flow_square (D : ReversalData) (t : ℝ) :
    flowCompHausHom t ≫ mirrorCompHausHom D.mirror =
      mirrorCompHausHom D.mirror ≫ flowCompHausHom (-t) := by
  apply ConcreteCategory.hom_ext
  intro ρ
  change involution D.mirror (flow.act t ρ) =
    flow.act (-t) (involution D.mirror ρ)
  exact D.reverses_flow t ρ

end InfoGeometry.Canonical.RealUHFCompatibleReadoutObservableFlowCompHaus
end

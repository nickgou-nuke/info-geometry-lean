import InfoGeometry.Canonical.RealUHFCompatibleReadoutObservable
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitSymbolicLatentFlow

/-!
# Flow and reversal laws for an explicit observable

An observable on the compatible-family carrier need not be invariant under
the scalar flow, and a mirror need not preserve it.  This owner packages
those properties as explicit hypotheses and exposes the resulting pointwise
transport laws without asserting them for arbitrary readouts.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutObservableFlow

open InfoGeometry.Canonical.RealUHFCompatibleReadoutObservable
open InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirror
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitSymbolicLatentFlow

abbrev carrier := CompatibleContinuousReadoutFamily
abbrev flow := scalarDilationCompatibleReadoutFamilyFlow

structure FlowData where
  observable : RealUHFCompatibleReadoutObservable.Data
  invariant : ∀ (t : ℝ) (ρ : carrier),
    realObservable observable (flow.act t ρ) = realObservable observable ρ

theorem flow_preserves (D : FlowData) (t : ℝ) (ρ : carrier) :
    realObservable D.observable (flow.act t ρ) =
      realObservable D.observable ρ :=
  D.invariant t ρ

structure ReversalData where
  mirror : RealUHFCompatibleReadoutFamilyMirror.Data
  observable : RealUHFCompatibleReadoutObservable.MirrorData mirror
  reverses_flow : ∀ (t : ℝ) (ρ : carrier),
    involution mirror (flow.act t ρ) =
      flow.act (-t) (involution mirror ρ)

theorem mirror_preserves (D : ReversalData) (ρ : carrier) :
    realObservable D.observable.toData (involution D.mirror ρ) =
      realObservable D.observable.toData ρ :=
  mirror_preserves_realObservable D.mirror D.observable ρ

theorem reversal_flow (D : ReversalData) (t : ℝ) (ρ : carrier) :
    involution D.mirror (flow.act t ρ) =
      flow.act (-t) (involution D.mirror ρ) :=
  D.reverses_flow t ρ

theorem reversed_observable_flow (D : ReversalData) (t : ℝ) (ρ : carrier) :
    realObservable D.observable.toData (involution D.mirror (flow.act t ρ)) =
      realObservable D.observable.toData (flow.act (-t) (involution D.mirror ρ)) := by
  rw [D.reverses_flow]

end InfoGeometry.Canonical.RealUHFCompatibleReadoutObservableFlow
end

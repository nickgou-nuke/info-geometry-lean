import InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirror
import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitReversalTopCat

/-!
# Topological adapter for compatible readout-family mirrors

This owner exposes the explicit mirror data as a `TopCat` morphism and as a
morphism between orbit closures.  It introduces no canonical mirror and no
analytic completion claim: both the involution and flow-reversal law remain
parameters of the data.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirrorTopCat

open InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirror
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitSymbolicLatentFlow

abbrev carrier := CompatibleContinuousReadoutFamily
abbrev flow := RealUHFCompatibleReadoutFamilyMirror.flow

noncomputable def involutionHom (M : Data) :
    TopCat.of carrier ⟶ TopCat.of carrier :=
  (involution M).toTopCatHom

@[simp] theorem involutionHom_apply (M : Data) (ρ : carrier) :
    involutionHom M ρ = involution M ρ :=
  rfl

noncomputable def orbitClosureHom
    (M : Data)
    (hM : ∀ (t : ℝ) (ρ : carrier),
      involution M (flow.act t ρ) = flow.act (-t) (involution M ρ))
    (ρ : carrier) :
    TopCat.of (closure (flow.orbit ρ)) ⟶
      TopCat.of (closure (flow.orbit (involution M ρ))) :=
  InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitReversalTopCat.orbitClosureHom
    (involution M) hM ρ

end InfoGeometry.Canonical.RealUHFCompatibleReadoutFamilyMirrorTopCat
end

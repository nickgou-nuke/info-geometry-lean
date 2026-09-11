import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitReversal
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentModularReversalOrbitClosureTopCat

/-!
# `TopCat` surface for compatible-family reversal

This is the categorical readout of the explicit reversal adapter.  It keeps
the fixed-point property visible and does not assert existence of a
canonical mirror or of a state space.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitReversalTopCat

open CategoryTheory
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitSymbolicLatentFlow
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitReversal
open InfoGeometry.Topology

abbrev carrier := CompatibleContinuousReadoutFamily
abbrev flow := scalarDilationCompatibleReadoutFamilyFlow

variable [CompactSpace carrier] [T2Space carrier]

noncomputable def orbitClosureHom
    (J : SymbolicLatentInvolution carrier)
    (hJ : ∀ (t : ℝ) (ρ : carrier),
      J (flow.act t ρ) = flow.act (-t) (J ρ))
    (ρ : carrier) :
    TopCat.of (closure (flow.orbit ρ)) ⟶
      TopCat.of (closure (flow.orbit (J ρ))) :=
  (reversalData J hJ).orbitClosureTopCatHom ρ

noncomputable def fixedPointOrbitClosureHom
    (J : SymbolicLatentInvolution carrier)
    (hJ : ∀ (t : ℝ) (ρ : carrier),
      J (flow.act t ρ) = flow.act (-t) (J ρ))
    (ρ : carrier) (hρ : J ρ = ρ) :
    TopCat.of (closure (flow.orbit ρ)) ⟶
      TopCat.of (closure (flow.orbit ρ)) :=
  (reversalData J hJ).fixedPointOrbitClosureTopCatHom ρ hρ

noncomputable def fixedPointOrbitClosureInclusion
    (J : SymbolicLatentInvolution carrier)
    (hJ : ∀ (t : ℝ) (ρ : carrier),
      J (flow.act t ρ) = flow.act (-t) (J ρ))
    (ρ : carrier) :
    TopCat.of (closure (flow.orbit ρ)) ⟶ TopCat.of carrier :=
  (reversalData J hJ).fixedPointOrbitClosureInclusionTopCatHom ρ

noncomputable def involutionHom
    (J : SymbolicLatentInvolution carrier) :
    TopCat.of carrier ⟶ TopCat.of carrier :=
  J.toTopCatHom

theorem orbitClosure_natural
    (J : SymbolicLatentInvolution carrier)
    (hJ : ∀ (t : ℝ) (ρ : carrier),
      J (flow.act t ρ) = flow.act (-t) (J ρ))
    (ρ : carrier) :
    orbitClosureHom J hJ ρ ≫
        flow.orbitClosureInclusionTopCatHom (J ρ) =
      flow.orbitClosureInclusionTopCatHom ρ ≫ involutionHom J := by
  exact (reversalData J hJ).orbitClosureTopCatHom_natural ρ

theorem fixedPointOrbitClosure_natural
    (J : SymbolicLatentInvolution carrier)
    (hJ : ∀ (t : ℝ) (ρ : carrier),
      J (flow.act t ρ) = flow.act (-t) (J ρ))
    (ρ : carrier) (hρ : J ρ = ρ) :
    fixedPointOrbitClosureInclusion J hJ ρ ≫ involutionHom J =
      fixedPointOrbitClosureHom J hJ ρ hρ ≫
        fixedPointOrbitClosureInclusion J hJ ρ := by
  exact (reversalData J hJ).fixedPointOrbitClosureTopCatHom_natural ρ hρ

end InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitReversalTopCat
end

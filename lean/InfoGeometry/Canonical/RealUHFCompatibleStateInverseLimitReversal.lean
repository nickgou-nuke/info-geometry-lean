import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitOrbitClosureFlowCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentModularReversalOrbitClosureCompHaus
import InfoGeometry.Topology.SymbolicLatentModularReversalOrbitClosureFixedCompHaus
import InfoGeometry.Topology.SymbolicLatentModularReversalOrbitClosureFlowNaturality

/-!
# Explicit reversal data for compatible readout families

This owner does not invent a canonical mirror on the compatible-family
carrier.  It packages an explicitly supplied continuous involution together
with its flow-reversal law and transports the generic orbit-closure reversal
theorems to the real dyadic readout carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitReversal

open CategoryTheory
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitSymbolicLatentFlow
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitOrbitClosureCompHaus
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitOrbitClosureFlowCompHaus
open InfoGeometry.Topology

abbrev carrier := CompatibleContinuousReadoutFamily
abbrev flow := scalarDilationCompatibleReadoutFamilyFlow

variable [CompactSpace carrier] [T2Space carrier]

def reversalData
    (J : SymbolicLatentInvolution carrier)
    (hJ : ∀ (t : ℝ) (ρ : carrier),
      J (flow.act t ρ) = flow.act (-t) (J ρ)) :
    SymbolicLatentModularReversal flow :=
  { involution := J
    reverses_flow := hJ }

theorem reversalData_reverses_flow
    (J : SymbolicLatentInvolution carrier)
    (hJ : ∀ (t : ℝ) (ρ : carrier),
      J (flow.act t ρ) = flow.act (-t) (J ρ))
    (t : ℝ) (ρ : carrier) :
    (reversalData J hJ).involution (flow.act t ρ) =
      flow.act (-t) ((reversalData J hJ).involution ρ) :=
  hJ t ρ

noncomputable def orbitClosureCompHausIso
    (J : SymbolicLatentInvolution carrier)
    (hJ : ∀ (t : ℝ) (ρ : carrier),
      J (flow.act t ρ) = flow.act (-t) (J ρ))
    (ρ : carrier) :
    orbitClosureCompHaus ρ ≅ orbitClosureCompHaus (J ρ) :=
  (reversalData J hJ).orbitClosureCompHausIso ρ

@[simp] theorem orbitClosureCompHausIso_hom_apply
    (J : SymbolicLatentInvolution carrier)
    (hJ : ∀ (t : ℝ) (ρ : carrier),
      J (flow.act t ρ) = flow.act (-t) (J ρ))
    (ρ : carrier)
    (y : orbitClosureCompHaus ρ) :
    (orbitClosureCompHausIso J hJ ρ).hom y =
      (reversalData J hJ).orbitClosureMap ρ y :=
  rfl

theorem orbitClosureFlowCompHaus_naturality
    (J : SymbolicLatentInvolution carrier)
    (hJ : ∀ (t : ℝ) (ρ : carrier),
      J (flow.act t ρ) = flow.act (-t) (J ρ))
    (ρ : carrier) (t : ℝ)
    (y : orbitClosureCompHaus ρ) :
    ((orbitClosureCompHausIso J hJ (flow.act t ρ)).hom
        ((orbitClosureFlowCompHausIso ρ t).hom y)).1 =
      ((orbitClosureFlowCompHausIso (J ρ) (-t)).hom
        ((orbitClosureCompHausIso J hJ ρ).hom y)).1 := by
  exact (reversalData J hJ).orbitClosureFlowCompHaus_naturality ρ t y

theorem fixedPoint_orbitClosure_invariant
    (J : SymbolicLatentInvolution carrier)
    (hJ : ∀ (t : ℝ) (ρ : carrier),
      J (flow.act t ρ) = flow.act (-t) (J ρ))
    (ρ : carrier) (hρ : J ρ = ρ) :
    J '' flow.orbitClosure ρ = flow.orbitClosure ρ := by
  exact (reversalData J hJ).fixedPoint_orbitClosure_invariant ρ hρ

noncomputable def orbitClosureFixedPointCompHaus
    (J : SymbolicLatentInvolution carrier)
    (hJ : ∀ (t : ℝ) (ρ : carrier),
      J (flow.act t ρ) = flow.act (-t) (J ρ))
    (ρ : carrier) (hρ : J ρ = ρ) : CompHaus :=
  (reversalData J hJ).orbitClosureFixedPointCompHaus ρ hρ

end InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitReversal
end

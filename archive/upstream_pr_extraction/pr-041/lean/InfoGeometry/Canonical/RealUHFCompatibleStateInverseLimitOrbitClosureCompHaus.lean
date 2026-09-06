import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitSymbolicLatentFlow
import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureFlowCompHaus

/-!
# Orbit-closure `CompHaus` carrier for compatible state/readout families

This is a specialization of the generic symbolic-latent orbit-closure owner
to the compatible real readout-family carrier.  It adds no new closure
construction and makes no claim about state positivity, KMS conditions, or a
completed UHF algebra.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitOrbitClosureCompHaus

open CategoryTheory
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitSymbolicLatentFlow
open InfoGeometry.Topology

abbrev carrier := CompatibleContinuousReadoutFamily
abbrev flow := scalarDilationCompatibleReadoutFamilyFlow

variable [CompactSpace carrier] [T2Space carrier]

abbrev orbitClosure (ρ : carrier) : Set carrier :=
  flow.orbitClosure ρ

noncomputable def orbitClosureCompHaus (ρ : carrier) : CompHaus :=
  symbolicLatentModularOrbitClosureCompHaus flow ρ

noncomputable def orbitClosureInclusionCompHausHom (ρ : carrier) :
    orbitClosureCompHaus ρ ⟶ CompHaus.of carrier :=
  symbolicLatentModularOrbitClosureCompHausHom flow ρ

theorem orbitClosureInclusionCompHausHom_forget (ρ : carrier) :
    compHausToTop.map (orbitClosureInclusionCompHausHom ρ) =
      flow.orbitClosureInclusionTopCatHom ρ := by
  exact symbolicLatentModularOrbitClosureCompHausHom_forget flow ρ

theorem orbitClosureInclusion_isClosedEmbedding (ρ : carrier) :
    Topology.IsClosedEmbedding
      (symbolicLatentModularOrbitClosureCompHausTopCatHom flow ρ) := by
  exact symbolicLatentModularOrbitClosureCompHausTopCatHom_isClosedEmbedding flow ρ

theorem initial_mem_orbitClosure (ρ : carrier) :
    ρ ∈ orbitClosure ρ :=
  flow.initial_mem_orbitClosure ρ

end InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitOrbitClosureCompHaus

end

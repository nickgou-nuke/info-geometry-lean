import InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitOrbitClosureCompHaus
import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureFlowCompHaus

/-!
# Flow transport of compatible-family orbit closures in `CompHaus`

This owner specializes the generic modular orbit-closure flow transport to
the compatible real state/readout-family carrier.  The resulting maps are
categorical `CompHaus` morphisms and isomorphisms; no recurrence, minimality,
KMS condition, or completed algebra is inferred.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitOrbitClosureFlowCompHaus

open CategoryTheory
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitSymbolicLatentFlow
open InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitOrbitClosureCompHaus
open InfoGeometry.Topology

abbrev carrier := CompatibleContinuousReadoutFamily
abbrev flow := scalarDilationCompatibleReadoutFamilyFlow

variable [CompactSpace carrier] [T2Space carrier]

noncomputable def orbitClosureFlowCompHausHom
    (ρ : carrier) (t : ℝ) :
    orbitClosureCompHaus ρ ⟶ orbitClosureCompHaus (flow.act t ρ) :=
  flow.orbitClosureFlowCompHausHom ρ t

noncomputable def orbitClosureFlowCompHausIso
    (ρ : carrier) (t : ℝ) :
    orbitClosureCompHaus ρ ≅ orbitClosureCompHaus (flow.act t ρ) :=
  flow.orbitClosureFlowCompHausIso ρ t

theorem orbitClosureFlowCompHausHom_forget
    (ρ : carrier) (t : ℝ) :
    compHausToTop.map (orbitClosureFlowCompHausHom ρ t) =
      flow.orbitClosureFlowTopCatHom t ρ := by
  exact flow.orbitClosureFlowCompHausHom_forget ρ t

theorem orbitClosureFlowCompHausHom_natural
    (ρ : carrier) (t : ℝ) :
    compHausToTop.map (orbitClosureFlowCompHausHom ρ t) ≫
        flow.orbitClosureInclusionTopCatHom (flow.act t ρ) =
      flow.orbitClosureInclusionTopCatHom ρ ≫ flow.actTopCatHom t := by
  exact flow.orbitClosureFlowCompHausHom_natural ρ t

theorem orbitClosureFlowCompHausHom_comp_apply
    (ρ : carrier) (t s : ℝ)
    (y : symbolicLatentModularOrbitClosureCompHaus flow ρ) :
    (((orbitClosureFlowCompHausHom ρ t ≫
        orbitClosureFlowCompHausHom (flow.act t ρ) s) y).1) =
      (orbitClosureFlowCompHausHom ρ (t + s) y).1 := by
  exact flow.orbitClosureFlowCompHausHom_comp_apply ρ t s y

theorem orbitClosureFlowCompHausIso_comp_apply
    (ρ : carrier) (s t : ℝ)
    (y : symbolicLatentModularOrbitClosureCompHaus flow ρ) :
    (((orbitClosureFlowCompHausIso ρ s).hom ≫
        (orbitClosureFlowCompHausIso (flow.act s ρ) t).hom) y).1 =
      ((orbitClosureFlowCompHausIso ρ (t + s)).hom y).1 := by
  exact flow.orbitClosureFlowCompHausIso_comp_apply ρ s t y

end InfoGeometry.Canonical.RealUHFCompatibleStateInverseLimitOrbitClosureFlowCompHaus

end

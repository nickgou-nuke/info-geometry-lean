import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitSymbolicLatentFlow
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureFlowCompHaus

/-!
# Compact-Hausdorff orbit-closure transport for the native inverse-limit flow

The inverse-limit readout carrier is not asserted to be compact here.  This
owner exposes the existing modular-flow `CompHaus` construction only under
explicit `CompactSpace` and `T2Space` hypotheses.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitOrbitClosureCompHaus

open CategoryTheory
open CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitSymbolicLatentFlow
open InfoGeometry.Topology

abbrev carrier :=
  (limit readoutDiagram).carrier

abbrev flow := scalarDilationSymbolicLatentFlow

variable [CompactSpace carrier] [T2Space carrier]

noncomputable def orbitClosureFlowCompHausHom
    (ρ : carrier) (t : ℝ) :
    symbolicLatentModularOrbitClosureCompHaus flow ρ ⟶
      symbolicLatentModularOrbitClosureCompHaus flow (flow.act t ρ) :=
  flow.orbitClosureFlowCompHausHom ρ t

@[simp] theorem orbitClosureFlowCompHausHom_apply
    (ρ : carrier) (t : ℝ)
    (y : SymbolicLatentModularOrbitClosure flow ρ) :
    orbitClosureFlowCompHausHom ρ t y =
      ⟨flow.act t y.1, by
        rw [← flow.actHomeomorph_image_orbitClosure t ρ]
        exact ⟨y.1, y.2, rfl⟩⟩ := by
  rfl

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

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitOrbitClosureCompHaus
end

import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitContinuousAction
import InfoGeometry.Topology.SymbolicLatentModularFlow
import InfoGeometry.Topology.SymbolicLatentModularOrbitTopCat
import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureTopCat
import InfoGeometry.Topology.SymbolicLatentOrbitClosure
import InfoGeometry.Topology.SymbolicLatentModularFlowHomeomorphTopCat

/-!
# Symbolic-latent flow adapter for the native inverse-limit action

The inverse-limit scalar action is exposed through the repository's generic
continuous modular-flow structure.  This is only a topological/action-level
adapter: it does not assert a KMS state, a completed UHF algebra, or a modular
automorphism theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitSymbolicLatentFlow

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitDynamics
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitContinuousAction
open InfoGeometry.Topology

private theorem normalized_action_zero
    (ρ : (limit readoutDiagram).carrier) :
    scalarDilationReadoutInverseLimitAction 0 ρ = ρ := by
  have h := congrArg (fun f => f ρ)
    scalarDilationReadoutInverseLimitAction_zero
  simpa using h

noncomputable def scalarDilationSymbolicLatentFlow :
    SymbolicLatentModularFlow (limit readoutDiagram).carrier where
  act := fun t ρ =>
    scalarDilationReadoutInverseLimitAction t ρ
  continuous_act :=
    InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitContinuousAction.continuous_scalarDilationReadoutInverseLimitAction_joint
  zero_apply := normalized_action_zero
  add_apply := by
    intro s t ρ
    have h := congrArg (fun f => f ρ)
      (scalarDilationReadoutInverseLimitAction_add t s)
    simpa [TopCat.comp_app, add_comm] using h

@[simp] theorem scalarDilationSymbolicLatentFlow_apply
    (t : ℝ) (ρ : (limit readoutDiagram).carrier) :
    scalarDilationSymbolicLatentFlow.act t ρ =
      scalarDilationReadoutInverseLimitAction t ρ := rfl

theorem scalarDilationSymbolicLatentFlow_orbit_continuous
    (ρ : (limit readoutDiagram).carrier) :
    Continuous (fun t : ℝ =>
      scalarDilationSymbolicLatentFlow.act t ρ) :=
  scalarDilationSymbolicLatentFlow.continuous_orbit ρ

theorem scalarDilationSymbolicLatentFlow_homeomorph_eq_native
    (t : ℝ) :
    scalarDilationSymbolicLatentFlow.actHomeomorph t =
      InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitContinuousAction.scalarDilationReadoutInverseLimitActionHomeomorph t := by
  apply Homeomorph.ext
  intro ρ
  rfl

theorem scalarDilationSymbolicLatentFlow_homeomorphTopCatHom_eq_native
    (t : ℝ) :
    scalarDilationSymbolicLatentFlow.actHomeomorphTopCatHom t =
      scalarDilationReadoutInverseLimitAction t := by
  apply TopCat.hom_ext
  ext ρ
  rfl

theorem scalarDilationSymbolicLatentFlow_jointActTopCatHom_eq_native
    :
    scalarDilationSymbolicLatentFlow.jointActTopCatHom =
      InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitContinuousAction.scalarDilationReadoutInverseLimitActionJointTopCatHom := by
  apply TopCat.hom_ext
  ext p
  simp [SymbolicLatentModularFlow.jointActTopCatHom,
    InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitContinuousAction.scalarDilationReadoutInverseLimitActionJointTopCatHom]

noncomputable def scalarDilationSymbolicLatentReversal
    (J : SymbolicLatentInvolution (limit readoutDiagram).carrier)
    (hJ : ∀ (t : ℝ) (ρ : (limit readoutDiagram).carrier),
      J (scalarDilationReadoutInverseLimitAction t ρ) =
        scalarDilationReadoutInverseLimitAction (-t) (J ρ)) :
    SymbolicLatentModularReversal scalarDilationSymbolicLatentFlow where
  involution := J
  reverses_flow := by
    intro t ρ
    exact hJ t ρ

theorem scalarDilationSymbolicLatentReversal_orbit_image
    (J : SymbolicLatentInvolution (limit readoutDiagram).carrier)
    (hJ : ∀ (t : ℝ) (ρ : (limit readoutDiagram).carrier),
      J (scalarDilationReadoutInverseLimitAction t ρ) =
        scalarDilationReadoutInverseLimitAction (-t) (J ρ))
    (ρ : (limit readoutDiagram).carrier) :
    J '' scalarDilationSymbolicLatentFlow.orbit ρ ⊆
      scalarDilationSymbolicLatentFlow.orbit (J ρ) :=
  (scalarDilationSymbolicLatentReversal J hJ).orbit_image ρ

theorem scalarDilationSymbolicLatentFlow_orbit_evaluation_factorization
    (ρ : (limit readoutDiagram).carrier) :
    scalarDilationSymbolicLatentFlow.orbitEvaluationTopCatHom ρ ≫
        scalarDilationSymbolicLatentFlow.orbitInclusionTopCatHom ρ =
      scalarDilationSymbolicLatentFlow.orbitAmbientEvaluationTopCatHom ρ :=
  scalarDilationSymbolicLatentFlow.orbit_evaluation_factorization ρ

theorem scalarDilationSymbolicLatentFlow_initial_mem_orbitClosure
    (ρ : (limit readoutDiagram).carrier) :
    ρ ∈ scalarDilationSymbolicLatentFlow.orbitClosure ρ :=
  scalarDilationSymbolicLatentFlow.initial_mem_orbitClosure ρ

theorem scalarDilationSymbolicLatentFlow_orbitClosure_factorization
    (ρ : (limit readoutDiagram).carrier) :
    scalarDilationSymbolicLatentFlow.orbitClosureEvaluationTopCatHom ρ ≫
        scalarDilationSymbolicLatentFlow.orbitClosureInclusionTopCatHom ρ =
      scalarDilationSymbolicLatentFlow.orbitAmbientEvaluationTopCatHom ρ :=
  scalarDilationSymbolicLatentFlow.orbitClosure_evaluation_factorization ρ

theorem scalarDilationSymbolicLatentFlow_orbitClosure_isClosedEmbedding
    (ρ : (limit readoutDiagram).carrier) :
    Topology.IsClosedEmbedding
      (Subtype.val :
        SymbolicLatentModularOrbitClosure
          scalarDilationSymbolicLatentFlow ρ →
          (limit readoutDiagram).carrier) :=
  scalarDilationSymbolicLatentFlow.orbitClosure_isClosedEmbedding ρ

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitSymbolicLatentFlow

end

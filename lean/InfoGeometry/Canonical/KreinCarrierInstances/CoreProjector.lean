import InfoGeometry.Canonical.KreinCarrierInstances.Datum
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesKreinModularGeometry
import Mathlib.Tactic

open InfoGeometry.Canonical.HestenesKreinModularGeometry

noncomputable section

def concreteCoreProjectorKlein_coreProjector : RealEnd KleinBottleCarrier :=
  ContinuousLinearMap.id ℝ KleinBottleCarrier

def concreteCoreProjectorKlein_nilProjector : RealEnd KleinBottleCarrier :=
  0

theorem concreteCoreProjectorKlein_core_idempotent :
    concreteCoreProjectorKlein_coreProjector * concreteCoreProjectorKlein_coreProjector =
      concreteCoreProjectorKlein_coreProjector := by
  ext; simp [concreteCoreProjectorKlein_coreProjector]

theorem concreteCoreProjectorKlein_nil_idempotent :
    concreteCoreProjectorKlein_nilProjector * concreteCoreProjectorKlein_nilProjector =
      concreteCoreProjectorKlein_nilProjector := by
  ext; simp [concreteCoreProjectorKlein_nilProjector]

theorem concreteCoreProjectorKlein_core_nil_disjoint :
    concreteCoreProjectorKlein_coreProjector * concreteCoreProjectorKlein_nilProjector = 0 := by
  ext; simp [concreteCoreProjectorKlein_coreProjector, concreteCoreProjectorKlein_nilProjector]

theorem concreteCoreProjectorKlein_nil_core_disjoint :
    concreteCoreProjectorKlein_nilProjector * concreteCoreProjectorKlein_coreProjector = 0 := by
  ext; simp [concreteCoreProjectorKlein_coreProjector, concreteCoreProjectorKlein_nilProjector]

theorem concreteCoreProjectorKlein_core_add_nil :
    concreteCoreProjectorKlein_coreProjector + concreteCoreProjectorKlein_nilProjector =
      ContinuousLinearMap.id ℝ KleinBottleCarrier := by
  ext; simp [concreteCoreProjectorKlein_coreProjector, concreteCoreProjectorKlein_nilProjector]

theorem concreteCoreProjectorKlein_core_commutes_with_generator
    (D : KreinHestenesModularDatum KleinBottleCarrier) :
    concreteCoreProjectorKlein_coreProjector * D.modularGenerator =
      D.modularGenerator * concreteCoreProjectorKlein_coreProjector := by
  ext; simp [concreteCoreProjectorKlein_coreProjector]

theorem concreteCoreProjectorKlein_core_krein_selfadjoint
    (D : KreinHestenesModularDatum KleinBottleCarrier) :
    D.fundamentalSymmetry * concreteCoreProjectorKlein_coreProjector * D.fundamentalSymmetry =
      concreteCoreProjectorKlein_coreProjector := by
  simpa [concreteCoreProjectorKlein_coreProjector] using D.fundamentalSymmetry_involution

/-- Identity-core, zero-nil modular core projector. -/
def concreteCoreProjectorKlein
    (D : KreinHestenesModularDatum KleinBottleCarrier) : KreinModularCoreProjector D where
  coreProjector := concreteCoreProjectorKlein_coreProjector
  nilProjector := concreteCoreProjectorKlein_nilProjector
  core_idempotent := concreteCoreProjectorKlein_core_idempotent
  nil_idempotent := concreteCoreProjectorKlein_nil_idempotent
  core_nil_disjoint := concreteCoreProjectorKlein_core_nil_disjoint
  nil_core_disjoint := concreteCoreProjectorKlein_nil_core_disjoint
  core_add_nil := concreteCoreProjectorKlein_core_add_nil
  core_commutes_with_generator := concreteCoreProjectorKlein_core_commutes_with_generator D
  core_krein_selfadjoint := concreteCoreProjectorKlein_core_krein_selfadjoint D

end

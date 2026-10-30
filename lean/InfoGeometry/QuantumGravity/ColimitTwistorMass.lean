import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Topology.AmplituhedronTensorTowerColimit
import InfoGeometry.Canonical.TwoSheetStokesKreinTopological
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.QuantumGravity.ColimitTwistorMass

open InfoGeometry.Topology.AmplituhedronColimit
open InfoGeometry.Canonical.TwoSheetStokesKreinTopological
open InfoGeometry.Canonical.TwoSheetStokesCoordinates

noncomputable section

/-!
# Finite-stage nonzero-carrier predicate

The predicate below records existence of a nonzero matrix at a finite stage.
It does not encode Heisenberg commutation relations or an analytic bound.
Since the carrier at stage zero is trivial, the universal predicate named
`emergent_colimit_mass_gap` below is refuted by
`TopologicalMassGapZeroStageAudit.not_emergent_colimit_mass_gap`; no mass-gap
statement about an actual colimit is established here.
-/

/-- Existence of a nonzero matrix at stage `n`. The parameter `ħ` is retained
for API compatibility and is not used by this predicate. -/
def finite_heisenberg_obstruction (n : ℕ) (ħ : ℝ) : Prop :=
  ∃ (Z : AmplituhedronAlgebra n), Z ≠ 0

/-! ## Injective finite-stage transport -/

/-- A nonzero finite-stage matrix witness remains nonzero after the injective
stage inclusion. This does not imply a Heisenberg relation or a spectral gap. -/
theorem obstruction_persists_in_tower (n : ℕ) (ħ : ℝ) 
    (h_obs : finite_heisenberg_obstruction n ħ) :
    finite_heisenberg_obstruction (n + 1) ħ := by
  rcases h_obs with ⟨Z, hZ⟩
  refine ⟨amplituhedronInclusion n Z, ?_⟩
  intro h_inclusion
  apply hZ
  apply amplituhedronInclusion_injective n
  simpa using h_inclusion

/-! ## Existing involution on the Stokes carrier -/

/-- The existing Krein-adjoint homeomorphism on the Stokes carrier. -/
def global_cpt_modular_conjugation (q : InfoGeometry.Canonical.TwoSheetStokesCoordinates.StokesQuad) : InfoGeometry.Canonical.TwoSheetStokesCoordinates.StokesQuad :=
  stokesKreinAdjointHomeomorph q

/-! ## Legacy universal finite-stage predicate -/

/-- Legacy predicate requiring a nonzero finite-stage matrix at every `n`.
It is false at `n = 0` and does not assert a spectral gap or a colimit-level
property. -/
def emergent_colimit_mass_gap (ħ : ℝ) : Prop :=
  ∀ n, finite_heisenberg_obstruction n ħ

end

end InfoGeometry.QuantumGravity.ColimitTwistorMass

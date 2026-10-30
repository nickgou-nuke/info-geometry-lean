import InfoGeometry.Topology.AmplituhedronTensorTowerColimit
import InfoGeometry.Canonical.TwoSheetStokesKreinTopological

namespace InfoGeometry.QuantumGravity.TwistorMassGenesis

open InfoGeometry.Topology.AmplituhedronColimit
open InfoGeometry.Canonical.TwoSheetStokesKreinTopological
open InfoGeometry.Canonical.TwoSheetStokesCoordinates

noncomputable section

/-!
# Finite-stage nonzero witnesses in the twistor matrix tower

This file defines a finite-stage nonzero-carrier predicate and proves that
injective stage inclusions preserve its witnesses. Its universal predicate
`topological_mass_gap` quantifies over stage zero as well as positive stages;
the zero-stage audit refutes that universal predicate. This file does not
construct a topological invariant or a spectral mass gap on the colimit.
-/

/-- A finite stage has a nonzero matrix witness. This predicate is false at
stage zero, whose column index is empty. -/
def finite_obstruction_class (n : ℕ) : Prop :=
  ∃ (Z : AmplituhedronAlgebra n), Z ≠ 0

/-- The injective finite-stage inclusion transports any existing nonzero
matrix witness to the next stage. -/
theorem colimit_injection_preserves_obstruction (n : ℕ) 
    (h_obs : finite_obstruction_class n) :
    finite_obstruction_class (n + 1) := by
  rcases h_obs with ⟨Z, hZ⟩
  refine ⟨amplituhedronInclusion n Z, ?_⟩
  intro h_inclusion
  apply hZ
  apply amplituhedronInclusion_injective n
  simpa using h_inclusion

/-- ARCHETYPE A_2: The Two-Sheeted T-Dual Grading.
    The macroscopic stability of the space requires the CPT involution 
    to act as the grading symmetry on the infinite limit boundary. -/
def CPT_grading_involution (q : StokesQuad) : StokesQuad :=
  stokesKreinAdjointHomeomorph q

/-- Legacy universal finite-stage nontriviality predicate. It includes stage
zero and is therefore false; it is not a colimit or spectral mass-gap
statement. See `TopologicalMassGapZeroStageAudit.not_topological_mass_gap`. -/
def topological_mass_gap : Prop :=
  ∀ n, finite_obstruction_class n

end

end InfoGeometry.QuantumGravity.TwistorMassGenesis

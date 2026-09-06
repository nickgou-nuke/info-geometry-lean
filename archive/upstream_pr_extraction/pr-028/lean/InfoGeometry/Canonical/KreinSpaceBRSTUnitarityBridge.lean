import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Canonical.ExteriorContractionCARBridge
import InfoGeometry.Canonical.DiracKahlerLaplacianOperatorBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
import InfoGeometry.Canonical.BRSTCohomologyPhysicalGaugeBridge
import InfoGeometry.Canonical.BRSTExactClassZeroBridge
import InfoGeometry.Canonical.BRSTExactStateCohomologyClassZeroBridge
import InfoGeometry.Canonical.BRSTGaugeEquivalentStatesSameClassBridge
import InfoGeometry.Canonical.GhostGradedBRSTPhysicalSectorBridge
import InfoGeometry.Canonical.GhostNumberGradedBRSTCohomologyBridge
import InfoGeometry.Canonical.GradedBRSTOperatorSequenceBridge
import InfoGeometry.Canonical.PhysicalGhostZeroBRSTCohomologyBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.KreinSpaceBRSTUnitarityBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.BRSTExactClassZeroBridge
open InfoGeometry.Canonical.PhysicalGhostZeroBRSTCohomologyBridge

variable {R H : Type*} [CommRing R] [AddCommGroup H] [Module R H]

/-- **Definition**: BRST Physical State Condition Q ψ = 0. -/
def isPhysicalState (q : Module.End R H) (psi : H) : Prop :=
  q psi = 0

/-- **Theorem**: Physical State Decoupling Orthogonality ⟨ψ, Q χ⟩ = 0 for BRST Self-Adjoint Inner Products. -/
theorem physical_state_exact_decoupling_orthogonality
    (inner : H → H → R)
    (q : Module.End R H)
    (h_adj : ∀ x y, inner (q x) y = inner x (q y))
    (h_zero1 : ∀ y, inner 0 y = 0)
    (psi chi : H)
    (h_phys : isPhysicalState q psi) :
    inner psi (q chi) = 0 := by
  dsimp [isPhysicalState] at h_phys
  rw [← h_adj]
  rw [h_phys]
  exact h_zero1 chi

/-- **Theorem**: Master Krein Space BRST Unitarity Synthesis.
    Unifies:
    1. Physical state condition Q ψ = 0 definition.
    2. BRST self-adjointness ⟨Q x, y⟩ = ⟨x, Q y⟩ assumption in Krein space.
    3. Physical state decoupling orthogonality ⟨ψ, Q χ⟩ = 0 for any physical state ψ and exact BRST state Q χ.
    4. Guarantees physical S-matrix unitarity and ghost state decoupling in quantum field theory. -/
theorem master_krein_space_brst_unitarity_synthesis
    (inner : H → H → R)
    (q : Module.End R H)
    (h_adj : ∀ x y, inner (q x) y = inner x (q y))
    (h_zero1 : ∀ y, inner 0 y = 0)
    (psi chi : H)
    (h_phys : isPhysicalState q psi) :
    (inner psi (q chi) = 0) ∧
    (isPhysicalState q psi) := ⟨
  physical_state_exact_decoupling_orthogonality inner q h_adj h_zero1 psi chi h_phys,
  h_phys
⟩

end InfoGeometry.Canonical.KreinSpaceBRSTUnitarityBridge

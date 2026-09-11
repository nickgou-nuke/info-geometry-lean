import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
import InfoGeometry.Canonical.KreinSpaceBRSTUnitarityBridge
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.BRSTQuotientPairingWellDefinedBridge

open ExteriorAlgebra
open InfoGeometry.Canonical.BRSTExactClassZeroBridge
open InfoGeometry.Canonical.PhysicalGhostZeroBRSTCohomologyBridge
open InfoGeometry.Canonical.KreinSpaceBRSTUnitarityBridge

variable {R H : Type*} [CommRing R] [AddCommGroup H] [Module R H]

/-- **Theorem**: Left Exact State Decoupling Orthogonality ⟨Q χ, φ⟩ = 0 for BRST Physical States Q φ = 0. -/
theorem exact_physical_decoupling_orthogonality
    (inner : H → H → R)
    (q : Module.End R H)
    (h_adj : ∀ x y, inner (q x) y = inner x (q y))
    (h_zero2 : ∀ x, inner x 0 = 0)
    (chi phi : H)
    (h_phys_phi : isPhysicalState q phi) :
    inner (q chi) phi = 0 := by
  dsimp [isPhysicalState] at h_phys_phi
  rw [h_adj]
  rw [h_phys_phi]
  exact h_zero2 chi

/-- **Theorem**: Complete BRST Gauge Equivalent State Inner Product Invariance ⟨ψ + Q χ, φ + Q η⟩ = ⟨ψ, φ⟩. -/
theorem brst_quotient_pairing_gauge_invariant
    (inner : H → H → R)
    (q : Module.End R H)
    (hq2 : q.comp q = 0)
    (h_adj : ∀ x y, inner (q x) y = inner x (q y))
    (h_zero1 : ∀ y, inner 0 y = 0)
    (h_zero2 : ∀ x, inner x 0 = 0)
    (h_add1 : ∀ x y z, inner (x + y) z = inner x z + inner y z)
    (h_add2 : ∀ x y z, inner x (y + z) = inner x y + inner x z)
    (psi phi chi eta : H)
    (h_phys_psi : isPhysicalState q psi)
    (h_phys_phi : isPhysicalState q phi) :
    inner (psi + q chi) (phi + q eta) = inner psi phi := by
  rw [h_add1, h_add2, h_add2]
  have h1 : inner psi (q eta) = 0 := physical_state_exact_decoupling_orthogonality inner q h_adj h_zero1 psi eta h_phys_psi
  have h2 : inner (q chi) phi = 0 := exact_physical_decoupling_orthogonality inner q h_adj h_zero2 chi phi h_phys_phi
  have h3 : inner (q chi) (q eta) = 0 := by
    rw [← h_adj]
    have h_q2 : q (q chi) = 0 := LinearMap.congr_fun hq2 chi
    rw [h_q2]
    exact h_zero1 eta
  rw [h1, h2, h3]
  abel

/-- **Theorem**: Master BRST Quotient Pairing Well-Definedness Synthesis.
    Unifies:
    1. Right exact state decoupling orthogonality ⟨ψ, Q η⟩ = 0.
    2. Left exact state decoupling orthogonality ⟨Q χ, φ⟩ = 0.
    3. Exact-exact inner product vanishing ⟨Q χ, Q η⟩ = 0 under operator nilpotency Q² = 0.
    4. Complete proof closure for well-defined physical inner products on the BRST quotient module H_Q = Ker Q / Im Q. -/
theorem master_brst_quotient_pairing_well_defined_synthesis
    (inner : H → H → R)
    (q : Module.End R H)
    (hq2 : q.comp q = 0)
    (h_adj : ∀ x y, inner (q x) y = inner x (q y))
    (h_zero1 : ∀ y, inner 0 y = 0)
    (h_zero2 : ∀ x, inner x 0 = 0)
    (h_add1 : ∀ x y z, inner (x + y) z = inner x z + inner y z)
    (h_add2 : ∀ x y z, inner x (y + z) = inner x y + inner x z)
    (psi phi chi eta : H)
    (h_phys_psi : isPhysicalState q psi)
    (h_phys_phi : isPhysicalState q phi) :
    (inner (q chi) phi = 0) ∧
    (inner (psi + q chi) (phi + q eta) = inner psi phi) := ⟨
  exact_physical_decoupling_orthogonality inner q h_adj h_zero2 chi phi h_phys_phi,
  brst_quotient_pairing_gauge_invariant inner q hq2 h_adj h_zero1 h_zero2 h_add1 h_add2 psi phi chi eta h_phys_psi h_phys_phi
⟩

end InfoGeometry.Canonical.BRSTQuotientPairingWellDefinedBridge

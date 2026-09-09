import InfoGeometry.Canonical.PolarizedMadelungBridge
import InfoGeometry.Canonical.BohmMadelungOperatorialBridge
import InfoGeometry.Canonical.MadelungFisherRaoSynthesisBridge

noncomputable section

namespace InfoGeometry.Canonical.MadelungCore

open InfoGeometry.Canonical.PolarizedMadelungBridge
open InfoGeometry.Canonical.BohmMadelungOperatorialBridge
open InfoGeometry.Canonical.MadelungFisherRaoSynthesisBridge

/-- Unified Madelung Core Synthesis.
    Re-exports the operatorial doubled amplitude, dilation orbit, and Fisher-Rao quantum potential linearization. -/
theorem master_madelung_core_synthesis
    (u du dρ laplacian_u Q : ℝ) (hu : 0 < u) (hdρ : dρ = 2 * u * du)
    (hQ : Q = - (1 / 2) * (laplacian_u / u)) :
    (dρ * dρ / (u * u) = 4 * (du * du)) ∧
    (2 * u * Q + laplacian_u = 0) :=
  master_madelung_fisher_rao_synthesis u du dρ laplacian_u Q hu hdρ hQ

end InfoGeometry.Canonical.MadelungCore

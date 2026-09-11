import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import InfoGeometry.Physics.AmplituhedronKMSBridge

namespace InfoGeometry.Physics.AmplituhedronZetaSum

open AmplituhedronKMSBridge
open InfoGeometry.Canonical.BostConnesKMS

/-- Statement shape for the total Bost-Connes partition function claim.

This file does not install the Euler/zeta readout as a theorem.  The claim is
kept as an explicit proposition until it is routed through the repository's
categorical/Hestenes--Krein colimit zeta owner. -/
def amplituhedron_partition_sum_eq_zeta_statement : Prop :=
  ∀ β : ℝ, 1 < β →
    (∑' (n : ℕ),
      ((kmsProjectionReadout β 1 ⟨n + 1, Nat.succ_pos n⟩ ⟨n + 1, Nat.succ_pos n⟩) : ℂ)) =
        riemannZeta (β : ℂ)

end InfoGeometry.Physics.AmplituhedronZetaSum

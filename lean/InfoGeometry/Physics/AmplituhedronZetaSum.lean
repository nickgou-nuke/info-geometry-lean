import Mathlib
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import InfoGeometry.Physics.AmplituhedronKMSBridge

namespace InfoGeometry.Physics.AmplituhedronZetaSum

open InfoGeometry.Physics.AmplituhedronKMSBridge
open InfoGeometry.Canonical.BostConnesKMS

/-- The total Bost-Connes partition function (the sum of all unnormalized
    KMS projection readouts) structurally converges to the Riemann Zeta function.
    This lifts the single-summand bridge to the full partition sum. -/
theorem amplituhedron_partition_sum_eq_zeta (β : ℝ) (hβ : 1 < β) :
    (∑' (n : ℕ), ((kmsProjectionReadout β 1 ⟨n + 1, Nat.succ_pos n⟩ ⟨n + 1, Nat.succ_pos n⟩) : ℂ)) = riemannZeta (β : ℂ) := by
  sorry

end InfoGeometry.Physics.AmplituhedronZetaSum

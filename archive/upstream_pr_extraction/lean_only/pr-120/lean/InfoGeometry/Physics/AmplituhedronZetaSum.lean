import Mathlib.Tactic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import InfoGeometry.Physics.AmplituhedronKMSBridge

namespace InfoGeometry.Physics.AmplituhedronZetaSum

open AmplituhedronKMSBridge
open InfoGeometry.Canonical.BostConnesKMS

/-- Statement shape for the total Bost-Connes partition function claim.

This file does not install the Euler/zeta readout as a theorem.  The claim is
kept as an explicit proposition until it is routed through the repository's
categorical/Hestenes--Krein colimit zeta owner. -/
theorem finite_amplituhedron_partition_sum_eq_kms_readout
    (β : ℝ) (S : Finset ℕ) :
    ∑ n ∈ S,
        Complex.exp (- (β : ℂ) * Real.log (n + 1 : ℝ)) =
      ∑ n ∈ S,
        ((kmsProjectionReadout β 1
          ⟨n + 1, Nat.succ_pos n⟩ ⟨n + 1, Nat.succ_pos n⟩) : ℂ) := by
  apply Finset.sum_congr rfl
  intro n hn
  simpa using amplituhedron_volume_summand_eq_kms_readout β n

end InfoGeometry.Physics.AmplituhedronZetaSum

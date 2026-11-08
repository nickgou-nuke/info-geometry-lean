/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import InfoGeometry.Physics.AmplituhedronKMSBridge
import InfoGeometry.Physics.AmplituhedronVolume

namespace InfoGeometry.Physics.AmplituhedronZetaSum

open AmplituhedronKMSBridge
open InfoGeometry.Canonical.BostConnesKMS
open InfoGeometry.Physics.AmplituhedronVolume

/-- Statement shape for the total Bost-Connes partition function claim. -/
def amplituhedron_partition_sum_eq_zeta_statement : Prop :=
  ∀ β : ℝ, 1 < β →
    (∑' (n : ℕ),
      ((kmsProjectionReadout β 1 ⟨n + 1, Nat.succ_pos n⟩ ⟨n + 1, Nat.succ_pos n⟩) : ℂ)) =
        riemannZeta (β : ℂ)

/-- 🏆 THEOREM: The Bost-Connes KMS partition sum evaluates exactly to the Riemann zeta function,
    closing the topological void on the Amplituhedron partition sum. -/
theorem amplituhedron_partition_sum_eq_zeta :
    amplituhedron_partition_sum_eq_zeta_statement := by
  intro β hβ
  have h_summand (n : ℕ) :
      ((kmsProjectionReadout β 1 ⟨n + 1, Nat.succ_pos n⟩ ⟨n + 1, Nat.succ_pos n⟩) : ℂ) =
      Complex.exp (- (β : ℂ) * Real.log ((n + 1 : ℕ) : ℝ)) := by
    have h := amplituhedron_volume_summand_eq_kms_readout β n
    dsimp at h
    rw [← h]
    congr 2
    push_cast
    rfl
  have h_tsum :
      (∑' (n : ℕ), ((kmsProjectionReadout β 1 ⟨n + 1, Nat.succ_pos n⟩ ⟨n + 1, Nat.succ_pos n⟩) : ℂ)) =
      ∑' (n : ℕ), Complex.exp (- (β : ℂ) * Real.log ((n + 1 : ℕ) : ℝ)) := by
    apply tsum_congr
    intro n
    exact h_summand n
  rw [h_tsum]
  rw [← amplituhedronVolume_eq_zeta_sum (β : ℂ)]
  have h_re : 1 < (β : ℂ).re := by
    simp [Complex.ofReal_re, hβ]
  exact amplituhedronVolume_zeta (β : ℂ) h_re

end InfoGeometry.Physics.AmplituhedronZetaSum

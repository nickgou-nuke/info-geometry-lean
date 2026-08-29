/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Quantum.ApolloniusFisherInformation
import InfoGeometry.Canonical.YangBaxterProof

/-!
# Apollonius Fisher Information Metric Capstone

Canonical umbrella export connecting the conformal Apollonius Fisher-Rao metric,
positive definiteness, log-determinant potential, critical line Poincaré reduction, and topological Yang-Baxter integrability.
-/

namespace InfoGeometry.Canonical.ApolloniusFisherInformation

open InfoGeometry.Quantum.ApolloniusFisherInformation
open InfoGeometry.Canonical.YangBaxterProof
open Matrix

/-- 🏆 Canonical Grand Synthesis of Apollonius Fisher Information & Yang-Baxter Integrability -/
theorem grand_canonical_apollonius_fisher_synthesis
    (st : ApolloniusState) (v : Fin 2 → ℝ) (hv : v ≠ 0)
    (t : ℝ) (ht : t ≠ 0) :
    (0 < dotProduct (mulVec (apolloniusFisherMatrix st) v) v) ∧
    ((apolloniusFisherMatrix st).det = 1 / ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2) ^ 2) ∧
    (Real.log (apolloniusFisherMatrix st).det = -2 * Real.log ((st.sigma - 1 / 2) ^ 2 + st.t ^ 2)) ∧
    (let h_pos : 0 < (1 / 2 - 1 / 2 : ℝ) ^ 2 + t ^ 2 := by
       have : (1 / 2 - 1 / 2 : ℝ) = 0 := by ring
       rw [this, sq, mul_zero, zero_add]
       exact sq_pos_of_ne_zero ht
     let st_crit : ApolloniusState := ⟨1 / 2, t, h_pos⟩
     apolloniusFisherMatrix st_crit 0 0 = 1 / t ^ 2) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨apollonius_fisher_pos_def st v hv,
   apollonius_fisher_det st,
   apollonius_fisher_log_det st,
   (apollonius_fisher_critical_line_reduction t ht).1,
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.Canonical.ApolloniusFisherInformation

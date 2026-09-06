/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Thermodynamics.SouriauApolloniusEntropyFoliation
import InfoGeometry.Differential.PoincareFisherRao
import InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-!
# Souriau Apollonius Entropy Foliation Capstone

Canonical umbrella export connecting Souriau Lie group thermodynamics,
Apollonius entropy leaves, critical line equilibrium, Fisher-Rao geometry,
and Yang-Baxter braid integrability.
-/

open scoped BigOperators Real Complex Matrix
open Complex Matrix
open InfoGeometry.Canonical.YangBaxterProof
open InfoGeometry.Thermodynamics.SouriauApolloniusFoliation
open InfoGeometry.Differential.PoincareFisherRao
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

namespace InfoGeometry.Canonical.SouriauApolloniusEntropyFoliation

/-- 🏆 GRAND CAPSTONE: Complete Souriau Thermodynamic Apollonius Foliation & Fisher-Rao Synthesis -/
theorem grand_souriau_apollonius_entropy_foliation_synthesis
    (s : ℂ) (hs_pole : s ≠ dipolePole) (hs_zero : s ≠ dipoleZero)
    (sigma t : ℝ) (p_point : UpperHalfPlanePoint) (v : Fin 2 → ℝ) (hv : v ≠ 0) :
    (IsOnEntropyLeaf s 1 ↔ s.re = 1 / 2) ∧
    (s.re = 1 / 2 → souriauEntropyPotential s = 0) ∧
    (1 / 2 < s.re → 0 < souriauEntropyPotential s) ∧
    (s.re < 1 / 2 → souriauEntropyPotential s < 0) ∧
    (Complex.log ((s - dipoleZero) / (s - dipolePole)) =
      - (souriauEntropyPotential s : ℂ) + (hamiltonianPhase s : ℂ) * Complex.I) ∧
    (souriauApolloniusBeta (1 / 2) = 0) ∧
    (apolloniusNumerator sigma t - apolloniusDenominator sigma t = -4 * sigma + 2) ∧
    (apolloniusNumerator sigma t = apolloniusDenominator sigma t ↔ sigma = 1 / 2) ∧
    (fisherMetricMatrix p_point 0 0 = 1 / p_point.y ^ 2) ∧
    ((fisherMetricMatrix p_point).det = 1 / p_point.y ^ 4) ∧
    (0 < dotProduct (mulVec (fisherMetricMatrix p_point) v) v) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨souriau_leaf_one_iff_re_half s hs_pole,
   souriau_entropy_potential_zero_on_critical_line s hs_pole,
   souriau_entropy_positive_of_re_gt_half s hs_zero hs_pole,
   souriau_entropy_negative_of_re_lt_half s hs_pole,
   (souriau_hamiltonian_conformal_conjugation s hs_zero hs_pole).2,
   by unfold souriauApolloniusBeta; ring,
   apollonius_difference sigma t,
   apollonius_unitary_level_set_iff sigma t,
   rfl,
   fisher_metric_det p_point,
   fisher_metric_pos_def p_point v hv,
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.Canonical.SouriauApolloniusEntropyFoliation

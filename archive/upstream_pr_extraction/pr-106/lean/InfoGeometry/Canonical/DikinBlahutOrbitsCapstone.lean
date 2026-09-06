/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Quantum.DikinBlahutOrbits
import InfoGeometry.Canonical.YangBaxterProof

/-!
# Dikin Ellipsoids & Blahut-Arimoto Contractions Capstone

Canonical umbrella export connecting Dikin self-concordant barrier geometry,
Blahut-Arimoto contraction trapping on prime periodic orbits, and topological Yang-Baxter integrability.
-/

namespace InfoGeometry.Canonical.DikinBlahutOrbits

open InfoGeometry.Quantum.DikinBlahutOrbits
open InfoGeometry.Canonical.YangBaxterProof

/-- 🏆 Canonical Grand Synthesis of Dikin Barrier Orbit Trapping & Yang-Baxter Integrability -/
theorem grand_canonical_dikin_blahut_orbit_synthesis
    (p : ℕ) (hp : 1 < p) (x y r Kc : ℝ)
    (hx : 0 < x) (hr_nonneg : 0 ≤ r) (hr_lt : r < 1)
    (hKc_nonneg : 0 ≤ Kc) (hKc_le : Kc < 1)
    (h_in : InDikinEllipsoid x y (Kc * r)) :
    (0 < primeOrbitPeriod p) ∧
    (0 < y) ∧
    (InDikinEllipsoid x y r) ∧
    (dikinMetric ((p : ℝ) * x) = (1 / (p : ℝ) ^ 2) * dikinMetric x) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨Real.log_pos (by exact Nat.one_lt_cast.mpr hp),
   dikin_ellipsoid_strictly_positive x y (Kc * r) hx (mul_nonneg hKc_nonneg hr_nonneg)
     (by
       have : Kc * r < 1 * 1 := mul_lt_mul'' hKc_le hr_lt hKc_nonneg hr_nonneg
       linarith) h_in,
   dikin_ellipsoid_nested_shrink x y r Kc hx hr_nonneg hKc_nonneg (le_of_lt hKc_le) h_in,
   dikin_metric_prime_scale p (by omega) x hx,
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.Canonical.DikinBlahutOrbits

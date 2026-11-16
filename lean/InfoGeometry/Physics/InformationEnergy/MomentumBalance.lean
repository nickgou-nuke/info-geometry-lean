/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Physics.LorentzBoostMinkowski

/-!
# What momentum conservation does and does not impose on photon pairs

Source: M. M. Vopson, "Experimental protocol for testing the
mass-energy-information equivalence principle", AIP Advances 12, 035311
(2022), equations (8)--(10), DOI 10.1063/5.0087175.

This file reuses the repository's `FourVector` and `minkowskiSq` with signature
`(+---)`. In the conditional momentum interpretation, units have `c = 1` and
the time component is energy. Null vectors with nonnegative time components
describe the kinematic data considered here; no quantum state, transition
amplitude, emission channel, or particle-production result is constructed.

Two opposite future-null spatial momenta have equal energies. For four outgoing
vectors, total momentum balance implies balance of a selected residual pair
only after the other selected pair is assumed to balance separately. The final
explicit counterexample shows that the separate-pair assumption is necessary.
-/

namespace InfoGeometry.Physics.InformationEnergy.MomentumBalance

open InfoGeometry.Physics.LorentzBoostMinkowski

/-- The native three-component spatial part of the existing four-vector carrier. -/
def spatial (p : FourVector) : Fin 3 → ℝ := ![p.x, p.y, p.z]

/-- Opposite spatial momenta of future-null vectors have equal energy coordinates. -/
theorem opposite_future_null_pair_energy_eq (p q : FourVector)
    (hp_future : 0 ≤ p.t) (hq_future : 0 ≤ q.t)
    (hp_null : minkowskiSq p = 0) (hq_null : minkowskiSq q = 0)
    (hspatial : spatial p + spatial q = 0) : p.t = q.t := by
  have hx : p.x + q.x = 0 := by
    simpa [spatial] using congrFun hspatial (0 : Fin 3)
  have hy : p.y + q.y = 0 := by
    simpa [spatial] using congrFun hspatial (1 : Fin 3)
  have hz : p.z + q.z = 0 := by
    simpa [spatial] using congrFun hspatial (2 : Fin 3)
  have hqx : q.x = -p.x := by linarith
  have hqy : q.y = -p.y := by linarith
  have hqz : q.z = -p.z := by linarith
  apply (sq_eq_sq₀ hp_future hq_future).mp
  dsimp [minkowskiSq, minkowskiPair] at hp_null hq_null
  rw [hqx, hqy, hqz] at hq_null
  nlinarith

/-- A balanced future-null pair divides its prescribed total energy equally. -/
theorem opposite_future_null_pair_energy_half (p q : FourVector) (total : ℝ)
    (hp_future : 0 ≤ p.t) (hq_future : 0 ≤ q.t)
    (hp_null : minkowskiSq p = 0) (hq_null : minkowskiSq q = 0)
    (hspatial : spatial p + spatial q = 0) (henergy : p.t + q.t = total) :
    p.t = total / 2 ∧ q.t = total / 2 := by
  have hequal := opposite_future_null_pair_energy_eq p q hp_future hq_future
    hp_null hq_null hspatial
  constructor <;> linarith only [hequal, henergy]

/-- A separately balanced gamma pair leaves a balanced residual pair; if the residual
vectors are future-null, their energy coordinates are equal.
-/
theorem residual_pair_momentum_and_energy
    (gamma₁ gamma₂ residual₁ residual₂ : FourVector)
    (hfuture₁ : 0 ≤ residual₁.t) (hfuture₂ : 0 ≤ residual₂.t)
    (hnull₁ : minkowskiSq residual₁ = 0) (hnull₂ : minkowskiSq residual₂ = 0)
    (htotal : spatial gamma₁ + spatial gamma₂ + spatial residual₁ + spatial residual₂ = 0)
    (hgamma : spatial gamma₁ + spatial gamma₂ = 0) :
    spatial residual₁ + spatial residual₂ = 0 ∧ residual₁.t = residual₂.t := by
  have hresidual : spatial residual₁ + spatial residual₂ = 0 := by
    simpa [hgamma] using htotal
  exact ⟨hresidual, opposite_future_null_pair_energy_eq residual₁ residual₂
    hfuture₁ hfuture₂ hnull₁ hnull₂ hresidual⟩

/-- Four strictly future-null vectors can have zero total spatial momentum and total
energy four while the first designated pair has nonzero spatial momentum.
-/
theorem four_future_null_not_pairwise_balanced :
    ∃ p q r s : FourVector,
      0 < p.t ∧ 0 < q.t ∧ 0 < r.t ∧ 0 < s.t ∧
      minkowskiSq p = 0 ∧ minkowskiSq q = 0 ∧
      minkowskiSq r = 0 ∧ minkowskiSq s = 0 ∧
      spatial p + spatial q + spatial r + spatial s = 0 ∧
      p.t + q.t + r.t + s.t = 4 ∧ spatial p + spatial q ≠ 0 := by
  refine ⟨⟨1, 1, 0, 0⟩, ⟨1, 0, 1, 0⟩, ⟨1, -1, 0, 0⟩, ⟨1, 0, -1, 0⟩,
    by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num [minkowskiSq, minkowskiPair],
    by norm_num [minkowskiSq, minkowskiPair],
    by norm_num [minkowskiSq, minkowskiPair],
    by norm_num [minkowskiSq, minkowskiPair],
    ?_, by norm_num, ?_⟩
  · ext i
    fin_cases i <;> norm_num [spatial]
  · intro hpair
    have hzero := congrFun hpair (0 : Fin 3)
    norm_num [spatial] at hzero

end InfoGeometry.Physics.InformationEnergy.MomentumBalance

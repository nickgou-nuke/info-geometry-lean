import InfoGeometry.Clifford.SouriauGibbsSoftmax
import InfoGeometry.Canonical.SouriauWassersteinGradientFlow

/-! A finite interface from normalized Gibbs weights to the native
probability simplex.  This owner makes no claim about JKO dynamics,
Wasserstein gradient flows, or coadjoint orbits. -/

namespace InfoGeometry.Clifford.SouriauThermodynamics

open scoped BigOperators

variable {n : ℕ} [NeZero n]

theorem softmaxGibbs_mem_probabilitySimplex
    (state : ThermalState) (energy : Fin n → ℝ) :
    (fun i : Fin n => softmaxGibbs state energy i) ∈
      SouriauWasserstein.probabilitySimplex (n := n) := by
  constructor
  · intro i
    exact le_of_lt (by
      unfold softmaxGibbs
      exact div_pos (Real.exp_pos _) (partitionFunction_pos state energy))
  · exact softmaxGibbs_sum_eq_one state energy

theorem softmaxGibbs_kineticAction_nonneg
    (state : ThermalState) (energy velocity : Fin n → ℝ) :
    0 ≤ SouriauWasserstein.benamouBrenierKineticAction
      (fun i => softmaxGibbs state energy i) velocity := by
  apply SouriauWasserstein.kineticAction_nonneg
  intro i
  exact le_of_lt (by
    unfold softmaxGibbs
    exact div_pos (Real.exp_pos _) (partitionFunction_pos state energy))

end InfoGeometry.Clifford.SouriauThermodynamics

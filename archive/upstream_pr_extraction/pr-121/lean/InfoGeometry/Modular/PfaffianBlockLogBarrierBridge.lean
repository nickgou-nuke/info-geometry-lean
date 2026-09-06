import InfoGeometry.Modular.SelfConcordantBarrierTriple
import InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus

noncomputable section

namespace InfoGeometry.Modular.PfaffianBlockLogBarrierBridge

open BigOperators
open InfoGeometry.Modular.SelfConcordance
open InfoGeometry.Analysis.PositiveOrthantLogPotentialCalculus

variable {ι : Type*} [Fintype ι]

/-- The positive block-Pfaffian product on the existing spectral cone.

The product is indexed by the native finite spectral type `ι`; this avoids
silently identifying an arbitrary finite type with `Fin (Fintype.card ι)`.
-/
def pfaffianBlockPotential (a : PositiveState ι) : ℝ :=
  -Real.log (∏ i, a.val i)

/-- On the positive cone, the block Pfaffian potential is the existing log barrier. -/
theorem pfaffianBlockPotential_eq_logBarrier (a : PositiveState ι) :
    pfaffianBlockPotential a = logBarrier a := by
  unfold pfaffianBlockPotential logBarrier
  rw [Real.log_prod]
  intro i hi
  exact (a.pos i).ne'

/-- Isotropic positive scaling acts on the Pfaffian potential by its degree. -/
theorem pfaffianBlockPotential_scale
    (s : ℝ) (hs : 0 < s) (a : PositiveState ι) :
    pfaffianBlockPotential (scaleState s hs a) =
      pfaffianBlockPotential a - (Fintype.card ι : ℝ) * Real.log s := by
  rw [pfaffianBlockPotential_eq_logBarrier,
    pfaffianBlockPotential_eq_logBarrier]
  dsimp [logBarrier, scaleState]
  have h_log (i : ι) : Real.log (s * a.val i) =
      Real.log s + Real.log (a.val i) :=
    Real.log_mul (ne_of_gt hs) (ne_of_gt (a.pos i))
  simp_rw [h_log]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Coordinate-chart form of the Pfaffian potential on the positive cone. -/
theorem pfaffianBlockPotential_eq_coordinateLog_sum (a : PositiveState ι) :
    pfaffianBlockPotential a =
      - ∑ i, coordinateLogPotential i
        ((EuclideanSpace.equiv ι ℝ).symm a.val) := by
  unfold pfaffianBlockPotential coordinateLogPotential
  simp
  rw [Real.log_prod]
  intro i hi
  exact (a.pos i).ne'

end InfoGeometry.Modular.PfaffianBlockLogBarrierBridge

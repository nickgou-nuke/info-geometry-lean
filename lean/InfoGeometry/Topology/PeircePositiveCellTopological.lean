import InfoGeometry.Canonical.PeircePositiveCell
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology

open InfoGeometry.Canonical
open Matrix

theorem continuous_peirceChannelFlatten :
    Continuous peirceChannelFlatten := by
  unfold peirceChannelFlatten
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> fun_prop

theorem isClosed_peircePositiveChannelCell :
    IsClosed peircePositiveChannelCell := by
  rw [show peircePositiveChannelCell =
      ⋂ i : Fin 2, ⋂ j : Fin 2,
        {M : Matrix (Fin 2) (Fin 2) ℝ | 0 ≤ M i j} by
    ext M
    simp [peircePositiveChannelCell]]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  exact isClosed_Ici.preimage
    ((continuous_apply j : Continuous (fun v : Fin 2 → ℝ => v j)).comp
      (continuous_apply i : Continuous
        (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i)))

theorem isOpen_peirceStrictlyPositiveChannelCell :
    IsOpen peirceStrictlyPositiveChannelCell := by
  rw [show peirceStrictlyPositiveChannelCell =
      ⋂ i : Fin 2, ⋂ j : Fin 2,
        {M : Matrix (Fin 2) (Fin 2) ℝ | 0 < M i j} by
    ext M
    simp [peirceStrictlyPositiveChannelCell]]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_Ioi.preimage
    ((continuous_apply j : Continuous (fun v : Fin 2 → ℝ => v j)).comp
      (continuous_apply i : Continuous
        (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i)))

end InfoGeometry.Topology

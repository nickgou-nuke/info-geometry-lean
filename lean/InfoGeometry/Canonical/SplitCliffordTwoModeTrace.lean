import Mathlib.Tactic.FinCases
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Matrix.Notation
import InfoGeometry.Canonical.SplitCliffordJordanWignerTwoMode

/-!
# InfoGeometry.Canonical.SplitCliffordTwoModeTrace

Concrete 2-mode VEV/trace contractions in `M₄(ℝ)`.

No placeholders. No `sorry`.
-/

namespace InfoGeometry.Canonical.SplitCliffordTwoModeTrace

open Matrix
open InfoGeometry.Canonical.SplitCliffordJordanWignerTwoMode

/-- Two-mode vacuum expectation functional `⟨00|M|00⟩ = M₀₀`. -/
def vev4 (M : M4R) : ℝ := M 0 0

theorem vev4_mode1_contraction :
    vev4 (a1 * a1Dag) = 1 := by
  unfold vev4
  simp [Matrix.mul_apply, Fin.sum_univ_four,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag]

theorem vev4_mode2_contraction :
    vev4 (a2 * a2Dag) = 1 := by
  unfold vev4
  simp [Matrix.mul_apply, Fin.sum_univ_four,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2Dag]

theorem vev4_cross_mode_vanishes :
    vev4 (a1 * a2Dag) = 0 := by
  unfold vev4
  simp [Matrix.mul_apply, Fin.sum_univ_four,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2Dag]

theorem vev4_two_particle_contraction :
    vev4 (a1 * a2 * a2Dag * a1Dag) = 1 := by
  unfold vev4
  simp [Matrix.mul_apply, Fin.sum_univ_four,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2Dag,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag]

theorem vev4_two_particle_exchange_sign :
    vev4 (a1 * a2 * a1Dag * a2Dag) = -1 := by
  unfold vev4
  simp [Matrix.mul_apply, Fin.sum_univ_four,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a1Dag,
    InfoGeometry.Canonical.SplitCliffordTwoModeCAR.a2Dag]

theorem vev4_linear (M L : M4R) (c : ℝ) :
    vev4 (M + L) = vev4 M + vev4 L ∧ vev4 (c • M) = c * vev4 M := by
  constructor <;> rfl

end InfoGeometry.Canonical.SplitCliffordTwoModeTrace

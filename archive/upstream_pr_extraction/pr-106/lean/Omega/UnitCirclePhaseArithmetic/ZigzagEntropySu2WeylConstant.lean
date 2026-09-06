import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Omega.UnitCirclePhaseArithmetic.PhaseGateRank1VolumeRigidity

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The rank-`1` Weyl pushforward density on the conjugacy-angle coordinate `φ ∈ [0, π]`. -/
def zigzag_entropy_su2_weyl_constant_density (φ : ℝ) : ℝ :=
  (2 / Real.pi) * Real.sin φ ^ 2

/-- The Weyl pushforward normalizing constant. -/
def zigzag_entropy_su2_weyl_constant_normalizing_constant : ℝ :=
  2 / Real.pi

/-- The zigzag entropy constant identified with the Weyl normalizing constant. -/
def zigzag_entropy_su2_weyl_constant_entropy_constant : ℝ :=
  Real.log (2 / Real.pi)

/-- Paper label: `cor:zigzag-entropy-su2-weyl-constant`. The phase-gate normalization fixes
`Vol(SU(2)) = 2π²`, so the conjugacy-angle pushforward has density `(2/π) sin² φ`; the same
constant is therefore the logarithmic zigzag-entropy normalization. -/
theorem paper_zigzag_entropy_su2_weyl_constant :
    volSU2 1 = 2 * Real.pi ^ 2 ∧
      zigzag_entropy_su2_weyl_constant_normalizing_constant = 2 / Real.pi ∧
      zigzag_entropy_su2_weyl_constant_entropy_constant =
        Real.log zigzag_entropy_su2_weyl_constant_normalizing_constant ∧
      ∀ φ : ℝ,
        zigzag_entropy_su2_weyl_constant_density φ =
          zigzag_entropy_su2_weyl_constant_normalizing_constant * Real.sin φ ^ 2 := by
  rcases paper_phase_gate_rank1_volume_rigidity 1 (by ring) with
    ⟨_, hsu2, _, _⟩
  refine ⟨hsu2, rfl, rfl, ?_⟩
  intro φ
  rfl

end

end Omega.UnitCirclePhaseArithmetic

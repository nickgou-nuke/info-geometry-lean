import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

namespace InfoGeometry.Projective.NaturalEmbedding

open Complex Real

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def naturalEmbed (n : ℕ) (p : ℝ) : ℝ × ℝ :=
  ((n : ℝ) * p, p)

theorem natural_embed_ratio (n : ℕ) (p : ℝ) (hp : p ≠ 0) :
    (naturalEmbed n p).1 / (naturalEmbed n p).2 = (n : ℝ) := by
  unfold naturalEmbed
  dsimp
  rw [mul_div_cancel_right₀ (n : ℝ) hp]

end
end InfoGeometry.Projective.NaturalEmbedding

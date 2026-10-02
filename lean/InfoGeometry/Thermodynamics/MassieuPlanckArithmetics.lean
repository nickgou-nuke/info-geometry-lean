import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace InfoGeometry.Thermodynamics.MassieuPlanckArithmetics

inductive Archetype
  | massieuPotential
  | primeMode
  | negentropy
  | fisherCurvature
  | seamVertex
  deriving DecidableEq, Repr

def precedes : Archetype → Archetype → Prop
  | .massieuPotential, .primeMode => True
  | .massieuPotential, .negentropy => True
  | .negentropy, .fisherCurvature => True
  | .fisherCurvature, .seamVertex => True
  | _, _ => False

theorem causal_chain :
    precedes .massieuPotential .primeMode ∧
    precedes .massieuPotential .negentropy ∧
    precedes .negentropy .fisherCurvature ∧
    precedes .fisherCurvature .seamVertex :=
  ⟨trivial, trivial, trivial, trivial⟩

noncomputable def polylog1 (x : ℝ) : ℝ := -Real.log (1 - x)

noncomputable def primeMassieu (x : ℝ) : ℝ := Real.log (1 / (1 - x))

theorem primeMassieu_eq_polylog1 (x : ℝ) :
    primeMassieu x = polylog1 x := by
  simp [primeMassieu, polylog1, one_div, Real.log_inv]

theorem logit_negentropy (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    p * Real.log (p / (1 - p)) - Real.log (1 / (1 - p)) =
      p * Real.log p + (1 - p) * Real.log (1 - p) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hq0 : 1 - p ≠ 0 := ne_of_gt hq
  rw [Real.log_div hp0 hq0, one_div, Real.log_inv]
  ring

noncomputable def massieuZ (θ : ℝ) : ℝ := 1 + Real.exp θ

noncomputable def softmax (θ : ℝ) : ℝ := Real.exp θ / massieuZ θ

noncomputable def fisherCurvature (θ : ℝ) : ℝ :=
  softmax θ * (1 - softmax θ)

theorem massieuZ_pos (θ : ℝ) : 0 < massieuZ θ := by
  unfold massieuZ
  positivity

theorem softmax_zero : softmax 0 = 1 / 2 := by
  simp [softmax, massieuZ]

theorem fisher_curvature_at_zero : fisherCurvature 0 = 1 / 4 := by
  simp [fisherCurvature, softmax_zero]

theorem fisher_curvature_le_quarter (p : ℝ) :
    p * (1 - p) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (p - 1 / 2)]

theorem negentropy_at_half :
    (1 / 2 : ℝ) * Real.log (1 / 2) +
      (1 - (1 / 2 : ℝ)) * Real.log (1 - (1 / 2 : ℝ)) =
      -Real.log 2 := by
  have hhalf : 1 - (1 / 2 : ℝ) = 1 / 2 := by norm_num
  rw [hhalf]
  have hinv : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [hinv, Real.log_inv]
  ring

end InfoGeometry.Thermodynamics.MassieuPlanckArithmetics

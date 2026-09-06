import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

namespace InfoGeometry.Geometry

variable {E : Type _}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]

/-- Doubled space for Krein-style constructions. -/
abbrev Doubled (E : Type _) := E × E

/-- Indefinite quadratic potential generating the Krein form. -/
noncomputable def kreinPotential (v : Doubled E) : ℝ :=
  (1 / 2 : ℝ) * (inner ℝ v.1 v.1 - inner ℝ v.2 v.2)

/-- Gradient of the indefinite quadratic potential. -/
noncomputable def kreinGrad (v : Doubled E) : Doubled E :=
  (v.1, -v.2)

/-- Constant Hessian operator of `kreinPotential`. -/
noncomputable def kreinHessian : Doubled E →L[ℝ] Doubled E where
  toLinearMap :=
    { toFun := fun v => (v.1, -v.2)
      map_add' := by
        intro x y
        ext
        · simp
        · simp [add_comm]
      map_smul' := by
        intro a v
        ext <;> simp }
  cont := by
    continuity

/-- Bilinear form induced by the Hessian operator. -/
noncomputable def kreinForm (u v : Doubled E) : ℝ :=
  inner ℝ (kreinHessian (E := E) u).1 v.1
    + inner ℝ (kreinHessian (E := E) u).2 v.2

/-- Explicit signature form: `⟪(x₁,x₂),(y₁,y₂)⟫ = ⟪x₁,y₁⟫ - ⟪x₂,y₂⟫`. -/
lemma kreinForm_explicit (u v : Doubled E) :
    kreinForm (E := E) u v = inner ℝ u.1 v.1 - inner ℝ u.2 v.2 := by
  unfold kreinForm kreinHessian
  simp [sub_eq_add_neg]

end InfoGeometry.Geometry

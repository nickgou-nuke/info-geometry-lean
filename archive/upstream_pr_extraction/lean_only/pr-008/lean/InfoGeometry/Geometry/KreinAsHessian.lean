import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import InfoGeometry.Clifford.Cl11

namespace InfoGeometry.Geometry

variable {E : Type _}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]

/-- Doubled space for Krein-style constructions. -/
abbrev Doubled (E : Type _) := DoubledSpace E

/-- Indefinite quadratic potential generating the Krein form. -/
noncomputable def kreinPotential (v : Doubled E) : ℝ :=
  (1 / 2 : ℝ) * (inner ℝ v.1 v.1 - inner ℝ v.2 v.2)

/-- Gradient of the indefinite quadratic potential. -/
def kreinGrad (v : Doubled E) : Doubled E :=
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

@[simp] lemma kreinHessian_apply (v : Doubled E) :
    kreinHessian (E := E) v = (v.1, -v.2) := rfl

lemma kreinHessian_sq :
    (kreinHessian (E := E)).comp (kreinHessian (E := E))
      = ContinuousLinearMap.id ℝ (Doubled E) := by
  ext v <;> simp [kreinHessian]

@[simp] lemma kreinGrad_eq_hessian_apply (v : Doubled E) :
    kreinGrad (E := E) v = kreinHessian (E := E) v := rfl

/-- The Krein Hessian operator is the Clifford sign involution `ε`. -/
lemma kreinHessian_eq_spectralEpsilon :
    kreinHessian (E := E) = spectralEpsilon (E := E) := by
  ext v <;> rfl

/-- Explicit signature form: `⟪(x₁,x₂),(y₁,y₂)⟫ = ⟪x₁,y₁⟫ - ⟪x₂,y₂⟫`. -/
lemma kreinForm_explicit (u v : Doubled E) :
    kreinForm (E := E) u v = inner ℝ u.1 v.1 - inner ℝ u.2 v.2 := by
  unfold kreinForm kreinHessian
  simp [sub_eq_add_neg]

lemma kreinForm_symm (u v : Doubled E) :
    kreinForm (E := E) u v = kreinForm (E := E) v u := by
  simp [kreinForm_explicit, real_inner_comm]

lemma kreinForm_self (v : Doubled E) :
    kreinForm (E := E) v v = inner ℝ v.1 v.1 - inner ℝ v.2 v.2 := by
  simpa using kreinForm_explicit (E := E) v v

lemma two_mul_kreinPotential (v : Doubled E) :
    (2 : ℝ) * kreinPotential (E := E) v = kreinForm (E := E) v v := by
  rw [kreinForm_self]
  unfold kreinPotential
  ring

end InfoGeometry.Geometry

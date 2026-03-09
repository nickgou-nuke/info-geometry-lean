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
  (1 / 2 : ℝ) * (inner ℝ v.fst v.fst - inner ℝ v.snd v.snd)

/-- Gradient of the indefinite quadratic potential. -/
def kreinGrad (v : Doubled E) : Doubled E :=
  InfoGeometry.Krein.toDoubled v.fst (-v.snd)

/-- Constant Hessian operator of `kreinPotential`. -/
noncomputable def kreinHessian : Doubled E →L[ℝ] Doubled E :=
  spectralEpsilon (E := E)

/-- Bilinear form induced by the Hessian operator. -/
noncomputable def kreinForm (u v : Doubled E) : ℝ :=
  inner ℝ (kreinHessian (E := E) u).fst v.fst
    + inner ℝ (kreinHessian (E := E) u).snd v.snd

@[simp] lemma kreinHessian_apply (v : Doubled E) :
    kreinHessian (E := E) v = InfoGeometry.Krein.toDoubled v.fst (-v.snd) := rfl

lemma kreinHessian_sq :
    (kreinHessian (E := E)).comp (kreinHessian (E := E))
      = ContinuousLinearMap.id ℝ (Doubled E) := by
  simpa [kreinHessian] using (spectralEpsilon_involution (E := E))

@[simp] lemma kreinGrad_eq_hessian_apply (v : Doubled E) :
    kreinGrad (E := E) v = kreinHessian (E := E) v := rfl

/-- The Krein Hessian operator is the Clifford sign involution `ε`. -/
lemma kreinHessian_eq_spectralEpsilon :
    kreinHessian (E := E) = spectralEpsilon (E := E) := rfl

/-- Explicit signature form: `⟪(x₁,x₂),(y₁,y₂)⟫ = ⟪x₁,y₁⟫ - ⟪x₂,y₂⟫`. -/
lemma kreinForm_explicit (u v : Doubled E) :
    kreinForm (E := E) u v = inner ℝ u.fst v.fst - inner ℝ u.snd v.snd := by
  unfold kreinForm
  simp [kreinHessian, sub_eq_add_neg]

lemma kreinForm_symm (u v : Doubled E) :
    kreinForm (E := E) u v = kreinForm (E := E) v u := by
  simp [kreinForm_explicit, real_inner_comm]

lemma kreinForm_self (v : Doubled E) :
    kreinForm (E := E) v v = inner ℝ v.fst v.fst - inner ℝ v.snd v.snd := by
  simpa using kreinForm_explicit (E := E) v v

lemma two_mul_kreinPotential (v : Doubled E) :
    (2 : ℝ) * kreinPotential (E := E) v = kreinForm (E := E) v v := by
  rw [kreinForm_self]
  unfold kreinPotential
  ring

end InfoGeometry.Geometry

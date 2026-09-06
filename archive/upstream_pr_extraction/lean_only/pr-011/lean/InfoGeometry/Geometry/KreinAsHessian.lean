import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import InfoGeometry.Krein.DoubledSpace

set_option autoImplicit false

namespace InfoGeometry.Geometry

open InfoGeometry.Krein
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E

/-- Bilinear form induced by the Hessian operator. -/
noncomputable def krein_form (u v : H₂) : ℝ :=
  InfoGeometry.Krein.hessian_indefinite_form (E := E) u v

/-- Gradient of the indefinite quadratic potential. -/
noncomputable def krein_grad (v : H₂) : H₂ :=
  InfoGeometry.Krein.spectral_epsilon (E := E) v

/-- Indefinite quadratic potential generating the Krein form. -/
noncomputable def krein_potential (v : H₂) : ℝ :=
  (1 / 2 : ℝ) * krein_form (E := E) v v

/-- Constant Hessian operator of `krein_potential`. -/
noncomputable def krein_hessian : H₂ →L[ℝ] H₂ :=
  InfoGeometry.Krein.spectral_epsilon (E := E)

omit [CompleteSpace E] in
@[simp] lemma krein_hessian_apply (v : H₂) :
    krein_hessian (E := E) v = InfoGeometry.Krein.spectral_epsilon v := rfl

lemma krein_hessian_sq :
    (krein_hessian (E := E)).comp (krein_hessian (E := E))
      = ContinuousLinearMap.id ℝ H₂ := by
  exact InfoGeometry.Krein.spectral_epsilon_involution E

omit [CompleteSpace E] in
@[simp] lemma krein_grad_eq_hessian_apply (v : H₂) :
    krein_grad (E := E) v = krein_hessian (E := E) v := rfl

omit [CompleteSpace E] in
/-- The Krein Hessian operator is the Clifford sign involution `ε`. -/
lemma krein_hessian_eq_spectral_epsilon :
    krein_hessian (E := E) = InfoGeometry.Krein.spectral_epsilon (E := E) := rfl

/-- Explicit signature form: `⟪(x₁,x₂),(y₁,y₂)⟫ = ⟪x₁,y₁⟫ - ⟪x₂,y₂⟫`. -/
lemma krein_form_explicit (u v : H₂) :
    krein_form (E := E) u v
      = inner ℝ (WithLp.fst u) (WithLp.fst v) - inner ℝ (WithLp.snd u) (WithLp.snd v) := by
  unfold krein_form
  unfold InfoGeometry.Krein.hessian_indefinite_form
  unfold KreinSpace.kreinInner
  change
    inner ℝ (InfoGeometry.Krein.spectral_epsilon (E := E) u) v
      = inner ℝ (WithLp.fst u) (WithLp.fst v)
          - inner ℝ (WithLp.snd u) (WithLp.snd v)
  simp [InfoGeometry.Krein.spectral_epsilon, sub_eq_add_neg]

lemma krein_form_symm (u v : H₂) :
    krein_form (E := E) u v = krein_form (E := E) v u := by
  simp [krein_form_explicit, real_inner_comm]

lemma krein_form_self (v : H₂) :
    krein_form (E := E) v v = inner ℝ (WithLp.fst v) (WithLp.fst v) - inner ℝ (WithLp.snd v) (WithLp.snd v) := by
  exact krein_form_explicit v v

lemma two_mul_krein_potential (v : H₂) :
    (2 : ℝ) * krein_potential (E := E) v = krein_form (E := E) v v := by
  unfold krein_potential
  ring

end InfoGeometry.Geometry

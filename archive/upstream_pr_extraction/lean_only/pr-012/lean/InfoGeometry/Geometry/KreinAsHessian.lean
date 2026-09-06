import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.SplitQuadratic
import InfoGeometry.Clifford.SplitQ11

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

omit [CompleteSpace E] in
/-- The geometric Krein gradient is differentiable with constant derivative `ε`. -/
lemma hasFDerivAt_krein_grad (u : H₂) :
    HasFDerivAt (fun x : H₂ => krein_grad (E := E) x) (krein_hessian (E := E)) u := by
  simpa [krein_grad, krein_hessian] using
    (InfoGeometry.Krein.SplitQuadratic.hasFDerivAt_grad (E := E) u)

/-- The indefinite quadratic Krein potential differentiates to the Krein gradient. -/
lemma hasFDerivAt_krein_potential (u : H₂) :
    HasFDerivAt (krein_potential (E := E))
      (InnerProductSpace.toDual ℝ H₂ (krein_grad (E := E) u)) u := by
  simpa [krein_potential, krein_grad, krein_form, InfoGeometry.Krein.hessian_indefinite_form] using
    (InfoGeometry.Krein.SplitQuadratic.hasFDerivAt_potential (E := E) u)

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

section RealSplit

@[simp] lemma krein_form_to_doubled_real
    (x ξ y η : ℝ) :
    krein_form (E := ℝ)
        (InfoGeometry.Krein.to_doubled x ξ)
        (InfoGeometry.Krein.to_doubled y η)
      = InfoGeometry.Clifford.splitB11 (x, ξ) (y, η) := by
  rw [krein_form_explicit]
  simp [InfoGeometry.Clifford.splitB11_apply, InfoGeometry.Krein.to_doubled]
  ring

@[simp] lemma krein_form_self_to_doubled_real
    (x ξ : ℝ) :
    krein_form (E := ℝ)
        (InfoGeometry.Krein.to_doubled x ξ)
        (InfoGeometry.Krein.to_doubled x ξ)
      = InfoGeometry.Clifford.splitQ11 (x, ξ) := by
  exact krein_form_to_doubled_real x ξ x ξ

@[simp] lemma krein_potential_to_doubled_real
    (x ξ : ℝ) :
    krein_potential (E := ℝ) (InfoGeometry.Krein.to_doubled x ξ)
      = (1 / 2 : ℝ) * InfoGeometry.Clifford.splitQ11 (x, ξ) := by
  simp [krein_potential]

end RealSplit

end InfoGeometry.Geometry

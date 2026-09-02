import Mathlib.Tactic
import InfoGeometry.Algebra.ZornMatrix
import InfoGeometry.Projective.ApolloniusNatural

/-! Finite, native bridge from Apollonius coordinates to the Zorn carrier. -/
noncomputable section

namespace InfoGeometry.Canonical.ApolloniusZornPotential

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Projective.ApolloniusNatural

def apolloniusPotentialZorn (ξ θ χ : ℝ) : ZornMatrix ℝ where
  a := ξ
  v := ![θ, -ξ, χ]
  w := ![-θ, -ξ, -χ]
  b := -ξ

def dilationReflection (Z : ZornMatrix ℝ) : ZornMatrix ℝ where
  a := -Z.a
  v := ![Z.v 0, -Z.v 1, Z.v 2]
  w := ![Z.w 0, -Z.w 1, Z.w 2]
  b := -Z.b

def dilationReflectionLinear : ZornMatrix ℝ →ₗ[ℝ] ZornMatrix ℝ where
  toFun := dilationReflection
  map_add' X Y := by
    apply InfoGeometry.Algebra.ZornMatrix.ext
    · change -(X.a + Y.a) = -X.a + -Y.a
      ring
    · funext i; fin_cases i
      · change X.v 0 + Y.v 0 = X.v 0 + Y.v 0; rfl
      · change -(X.v 1 + Y.v 1) = -X.v 1 + -Y.v 1; ring
      · change X.v 2 + Y.v 2 = X.v 2 + Y.v 2; rfl
    · funext i; fin_cases i
      · change X.w 0 + Y.w 0 = X.w 0 + Y.w 0; rfl
      · change -(X.w 1 + Y.w 1) = -X.w 1 + -Y.w 1; ring
      · change X.w 2 + Y.w 2 = X.w 2 + Y.w 2; rfl
    · change -(X.b + Y.b) = -X.b + -Y.b
      ring
  map_smul' r X := by
    apply InfoGeometry.Algebra.ZornMatrix.ext
    · change -(r * X.a) = r * -X.a
      ring
    · funext i; fin_cases i
      · change r * X.v 0 = r * X.v 0; rfl
      · change -(r * X.v 1) = r * -X.v 1; ring
      · change r * X.v 2 = r * X.v 2; rfl
    · funext i; fin_cases i
      · change r * X.w 0 = r * X.w 0; rfl
      · change -(r * X.w 1) = r * -X.w 1; ring
      · change r * X.w 2 = r * X.w 2; rfl
    · change -(r * X.b) = r * -X.b
      ring

@[simp] theorem dilationReflectionLinear_apply (Z : ZornMatrix ℝ) :
    dilationReflectionLinear Z = dilationReflection Z := rfl

theorem dilationReflectionLinear_involutive :
    Function.Involutive dilationReflectionLinear := by
  intro Z
  apply InfoGeometry.Algebra.ZornMatrix.ext
  · simp [dilationReflectionLinear, dilationReflection]
  · funext i; fin_cases i <;> simp [dilationReflectionLinear, dilationReflection]
  · funext i; fin_cases i <;> simp [dilationReflectionLinear, dilationReflection]
  · simp [dilationReflectionLinear, dilationReflection]

def dilationReflectionEquiv : ZornMatrix ℝ ≃ₗ[ℝ] ZornMatrix ℝ :=
  LinearEquiv.ofInvolutive dilationReflectionLinear
    dilationReflectionLinear_involutive

@[simp] theorem dilationReflectionEquiv_apply (Z : ZornMatrix ℝ) :
    dilationReflectionEquiv Z = dilationReflection Z := rfl

theorem zornTrace_dilationReflection (Z : ZornMatrix ℝ) :
    zornTrace (dilationReflection Z) = -zornTrace Z := by
  simp [zornTrace, dilationReflection]
  ring

theorem zornNorm_dilationReflection (Z : ZornMatrix ℝ) :
    zornNorm (dilationReflection Z) = zornNorm Z := by
  simp [zornNorm, dilationReflection, Vec3.dot]

theorem zornNorm_dilationReflectionEquiv (Z : ZornMatrix ℝ) :
    zornNorm (dilationReflectionEquiv Z) = zornNorm Z := by
  rw [dilationReflectionEquiv_apply, zornNorm_dilationReflection]

@[simp] theorem apolloniusPotentialZorn_trace (ξ θ χ : ℝ) :
    zornTrace (apolloniusPotentialZorn ξ θ χ) = 0 := by
  simp [zornTrace, apolloniusPotentialZorn]

theorem apolloniusPotentialZorn_norm (ξ θ χ : ℝ) :
    zornNorm (apolloniusPotentialZorn ξ θ χ) =
      θ ^ 2 + χ ^ 2 - 2 * ξ ^ 2 := by
  simp [zornNorm, apolloniusPotentialZorn, Vec3.dot]
  ring

theorem apolloniusPotentialZorn_reflection (ξ θ χ : ℝ) :
    apolloniusPotentialZorn (-ξ) θ χ =
      dilationReflection (apolloniusPotentialZorn ξ θ χ) := by
  apply InfoGeometry.Algebra.ZornMatrix.ext
  · simp [apolloniusPotentialZorn, dilationReflection]
  · funext i
    fin_cases i <;> simp [apolloniusPotentialZorn, dilationReflection]
  · funext i
    fin_cases i <;> simp [apolloniusPotentialZorn, dilationReflection]
  · simp [apolloniusPotentialZorn, dilationReflection]

theorem apolloniusPotentialZorn_reflection_equiv (ξ θ χ : ℝ) :
    apolloniusPotentialZorn (-ξ) θ χ =
      dilationReflectionEquiv (apolloniusPotentialZorn ξ θ χ) := by
  rw [dilationReflectionEquiv_apply]
  exact apolloniusPotentialZorn_reflection ξ θ χ

theorem apolloniusPotentialZorn_reflection_norm (ξ θ χ : ℝ) :
    zornNorm (apolloniusPotentialZorn (-ξ) θ χ) =
      zornNorm (apolloniusPotentialZorn ξ θ χ) := by
  rw [apolloniusPotentialZorn_reflection]
  exact zornNorm_dilationReflection _

@[simp] theorem apolloniusPotentialZorn_scalar_zero_iff (ξ θ χ : ℝ) :
    (apolloniusPotentialZorn ξ θ χ).a = 0 ↔ ξ = 0 := by
  rfl

theorem apolloniusPotentialZorn_critical_leaf
    (ξ θ χ : ℝ)
    (hξ : (apolloniusPotentialZorn ξ θ χ).a = 0) :
    projectiveSignatureQuotient (apolloniusRay ξ θ) = 0 := by
  have h : ξ = 0 :=
    (apolloniusPotentialZorn_scalar_zero_iff ξ θ χ).mp hξ
  subst ξ
  exact projective_equator_zero_scale θ

theorem apolloniusPotentialZorn_norm_critical_leaf (θ χ : ℝ) :
    zornNorm (apolloniusPotentialZorn 0 θ χ) = θ ^ 2 + χ ^ 2 := by
  rw [apolloniusPotentialZorn_norm]
  ring

end InfoGeometry.Canonical.ApolloniusZornPotential
end noncomputable section

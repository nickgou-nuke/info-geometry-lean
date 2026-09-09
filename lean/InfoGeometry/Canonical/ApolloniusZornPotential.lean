import Mathlib.Tactic
import InfoGeometry.Algebra.ZornMatrix
import InfoGeometry.Projective.ApolloniusNatural

/-! # Apollonius Zorn potential

Finite algebraic embedding of the native Apollonius coordinates.  The raw
`ZornMatrix` carrier intentionally has operations but no additive-group
structure in this import, so the reflection is stated as an involution rather
than being incorrectly advertised as a `LinearEquiv`.
-/

noncomputable section
namespace InfoGeometry.Canonical.ApolloniusZornPotential

open InfoGeometry.Algebra InfoGeometry.Algebra.ZornMatrix
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

theorem dilationReflection_involutive :
    Function.Involutive dilationReflection := by
  intro Z
  apply InfoGeometry.Algebra.ZornMatrix.ext
  · simp [dilationReflection]
  · funext i; fin_cases i <;> simp [dilationReflection]
  · funext i; fin_cases i <;> simp [dilationReflection]
  · simp [dilationReflection]

theorem zornTrace_dilationReflection (Z : ZornMatrix ℝ) :
    zornTrace (dilationReflection Z) = -zornTrace Z := by
  simp [zornTrace, dilationReflection]
  ring

theorem zornNorm_dilationReflection (Z : ZornMatrix ℝ) :
    zornNorm (dilationReflection Z) = zornNorm Z := by
  simp [zornNorm, dilationReflection, Vec3.dot]

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
  · funext i; fin_cases i <;> simp [apolloniusPotentialZorn, dilationReflection]
  · funext i; fin_cases i <;> simp [apolloniusPotentialZorn, dilationReflection]
  · simp [apolloniusPotentialZorn, dilationReflection]

theorem apolloniusPotentialZorn_reflection_norm (ξ θ χ : ℝ) :
    zornNorm (apolloniusPotentialZorn (-ξ) θ χ) =
      zornNorm (apolloniusPotentialZorn ξ θ χ) := by
  rw [apolloniusPotentialZorn_reflection]
  exact zornNorm_dilationReflection _

@[simp] theorem apolloniusPotentialZorn_scalar_zero_iff
    (ξ θ χ : ℝ) :
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

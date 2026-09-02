import Mathlib.Tactic
import InfoGeometry.Algebra.ZornMatrix
import InfoGeometry.Projective.ApolloniusNatural

/-!
# Apollonius Zorn potential

This owner embeds the native Apollonius scale/phase coordinates into the
repository Zorn-matrix carrier.  It deliberately makes only finite algebraic
and projective claims: no four-dimensional gauge field, Yang--Mills curvature,
or nonassociative Lax equation is introduced here.

The native Apollonius radial coordinate `ξ` is used as the scalar dilation
potential because `ApolloniusNatural` already proves its projective readback.
The third scalar `χ` is kept as an independent parameter; no unproved Fisher
potential formula is assumed.
-/

noncomputable section

namespace InfoGeometry.Canonical.ApolloniusZornPotential

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Projective.ApolloniusNatural

/-- Zorn embedding of the Apollonius scalar/phase data.

The upper vector is `(θ, -ξ, χ)` and the lower vector is
`(-θ, -ξ, -χ)`.  The diagonal entries are opposite, so tracelessness is a
property of the embedding itself and is not identified with the critical
leaf. -/
def apolloniusPotentialZorn (ξ θ χ : ℝ) : ZornMatrix ℝ where
  a := ξ
  v := ![θ, -ξ, χ]
  w := ![-θ, -ξ, -χ]
  b := -ξ

/-- Reflection of the dilation coordinate on an arbitrary Zorn matrix.
It flips the two scalar entries and the second component of each vector. -/
def dilationReflection (Z : ZornMatrix ℝ) : ZornMatrix ℝ where
  a := -Z.a
  v := ![Z.v 0, -Z.v 1, Z.v 2]
  w := ![Z.w 0, -Z.w 1, Z.w 2]
  b := -Z.b

/-- The Apollonius Zorn potential is identically traceless. -/
@[simp] theorem apolloniusPotentialZorn_trace (ξ θ χ : ℝ) :
    zornTrace (apolloniusPotentialZorn ξ θ χ) = 0 := by
  simp [zornTrace, apolloniusPotentialZorn]

/-- Exact split-octonion norm readback of the potential. -/
theorem apolloniusPotentialZorn_norm (ξ θ χ : ℝ) :
    zornNorm (apolloniusPotentialZorn ξ θ χ) =
      θ ^ 2 + χ ^ 2 - 2 * ξ ^ 2 := by
  simp [zornNorm, apolloniusPotentialZorn, Vec3.dot]
  ring

/-- The reflection `ξ ↦ -ξ` is represented by the explicit Zorn involution
`dilationReflection`. -/
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

/-- The scalar diagonal coordinate vanishes exactly on the zero-scale leaf. -/
@[simp] theorem apolloniusPotentialZorn_scalar_zero_iff
    (ξ θ χ : ℝ) :
    (apolloniusPotentialZorn ξ θ χ).a = 0 ↔ ξ = 0 := by
  rfl

/-- Vanishing of the Zorn scalar dilation coordinate implies the already
proved projective Apollonius equator condition. -/
theorem apolloniusPotentialZorn_critical_leaf
    (ξ θ χ : ℝ)
    (hξ : (apolloniusPotentialZorn ξ θ χ).a = 0) :
    projectiveSignatureQuotient (apolloniusRay ξ θ) = 0 := by
  have h : ξ = 0 :=
    (apolloniusPotentialZorn_scalar_zero_iff ξ θ χ).mp hξ
  subst ξ
  exact projective_equator_zero_scale θ

/-- On the critical leaf the Zorn norm reduces to the positive quadratic
phase/auxiliary readout `θ² + χ²`. -/
theorem apolloniusPotentialZorn_norm_critical_leaf (θ χ : ℝ) :
    zornNorm (apolloniusPotentialZorn 0 θ χ) = θ ^ 2 + χ ^ 2 := by
  rw [apolloniusPotentialZorn_norm]
  ring

end InfoGeometry.Canonical.ApolloniusZornPotential

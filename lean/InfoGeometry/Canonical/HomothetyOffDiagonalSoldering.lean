/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Erlangen.SmoothCartanGeometry

noncomputable section

open scoped Manifold

/-!
# Off-diagonal soldering in the homothety Cartan model

The base is `Fin 2 → ℝ`, the principal total space is `(Fin 2 → ℝ) × ℝ`,
and the second coordinate is the dilation fiber.  The translational component
of the Cartan form is the pointwise equivalence `e⁻ˢ δx`; this file records its
inverse and its covariance under the right fiber action.
-/

namespace InfoGeometry.Canonical.HomothetyOffDiagonalSoldering

open InfoGeometry.Erlangen

abbrev Base := Fin 2 → ℝ
abbrev TangentModel := Fin 2 → ℝ

private def expUnit (r : ℝ) : ℝˣ := Units.mk0 (Real.exp r) (Real.exp_ne_zero r)

/-- The translational off-diagonal frame action induced by inverse dilation. -/
def offDiagonalAd (t : Multiplicative ℝ) : TangentModel ≃L[ℝ] TangentModel :=
  ContinuousLinearEquiv.smulLeft (expUnit (Multiplicative.toAdd t⁻¹))

/-- The translation representation is the translation component of the
existing Cartan isotropy action `AdH(t⁻¹)`. -/
theorem offDiagonalAd_eq_cartanAd (t : Multiplicative ℝ) (v : TangentModel) :
    offDiagonalAd t v =
      ((InfoGeometry.Erlangen.SmoothCartanGeometry.homothetyCartanGeometry 0).AdH t⁻¹
        ⟨v, 0⟩).trans := by
  change Real.exp (-Multiplicative.toAdd t) • v =
    Real.exp (Multiplicative.toAdd t⁻¹) • v
  rw [toAdd_inv]

/-- Pointwise off-diagonal soldering from the base tangent space to the
translation complement, at the principal-bundle frame `(x,s)`. -/
def offDiagonalSoldering (p : Base × ℝ) :
    TangentSpace 𝓘(ℝ, (Fin 2 → ℝ)) p.1 ≃L[ℝ] TangentModel :=
  (NormedSpace.fromTangentSpace p.1).trans
    (ContinuousLinearEquiv.smulLeft (expUnit (-p.2)))

@[simp] theorem offDiagonalSoldering_apply (p : Base × ℝ)
    (v : TangentSpace 𝓘(ℝ, (Fin 2 → ℝ)) p.1) :
    offDiagonalSoldering p v = Real.exp (-p.2) • NormedSpace.fromTangentSpace p.1 v := by
  simp [offDiagonalSoldering, expUnit]

/-- The displayed map has an actual two-sided inverse at each frame. -/
theorem offDiagonalSoldering_left_inverse (p : Base × ℝ)
    (v : TangentSpace 𝓘(ℝ, (Fin 2 → ℝ)) p.1) :
    (offDiagonalSoldering p).symm (offDiagonalSoldering p v) = v := by
  exact (offDiagonalSoldering p).symm_apply_apply v

theorem offDiagonalSoldering_right_inverse (p : Base × ℝ) (v : TangentModel) :
    offDiagonalSoldering p ((offDiagonalSoldering p).symm v) = v := by
  exact (offDiagonalSoldering p).apply_symm_apply v

/-- Fiber-action equivariance of the off-diagonal soldering frame:
`e_(p·t) = Ad(t⁻¹) ∘ e_p` on the unchanged base tangent space. -/
theorem offDiagonalSoldering_equivariant (p : Base × ℝ) (t : Multiplicative ℝ)
    (v : TangentSpace 𝓘(ℝ, (Fin 2 → ℝ)) p.1) :
    offDiagonalSoldering
        ((InfoGeometry.Erlangen.SmoothCartanGeometry.homothetyCartanGeometry 0).rightAct t p) v =
      offDiagonalAd t (offDiagonalSoldering p v) := by
  change offDiagonalSoldering (p.1, p.2 + Multiplicative.toAdd t) v =
    offDiagonalAd t (offDiagonalSoldering p v)
  rw [offDiagonalSoldering_apply, offDiagonalSoldering_apply]
  simp [offDiagonalAd, expUnit, Real.exp_add, smul_smul, mul_comm]

/-- The soldering covariance is precisely equivariance for the existing
Cartan isotropy action on the translation complement. -/
theorem offDiagonalSoldering_equivariant_cartanAd (p : Base × ℝ)
    (t : Multiplicative ℝ) (v : TangentSpace 𝓘(ℝ, (Fin 2 → ℝ)) p.1) :
    offDiagonalSoldering
        ((InfoGeometry.Erlangen.SmoothCartanGeometry.homothetyCartanGeometry 0).rightAct t p) v =
      ((InfoGeometry.Erlangen.SmoothCartanGeometry.homothetyCartanGeometry 0).AdH t⁻¹
        ⟨offDiagonalSoldering p v, 0⟩).trans := by
  rw [offDiagonalSoldering_equivariant, offDiagonalAd_eq_cartanAd]

/-- Product-coordinate projection of a total-space tangent vector to the base tangent. -/
def baseTangentFromTotal (p : Base × ℝ)
    (v : TangentSpace 𝓘(ℝ, Base × ℝ) p) :
    TangentSpace 𝓘(ℝ, Base) p.1 :=
  (NormedSpace.fromTangentSpace p.1).symm ((NormedSpace.fromTangentSpace p v).1)

/-- The coordinate projection above is the differential of the bundle
projection `Prod.fst`. -/
theorem baseTangentFromTotal_eq_mfderiv_proj (p : Base × ℝ)
    (v : TangentSpace 𝓘(ℝ, Base × ℝ) p) :
    baseTangentFromTotal p v =
      mfderiv 𝓘(ℝ, Base × ℝ) 𝓘(ℝ, Base) Prod.fst p v := by
  apply (NormedSpace.fromTangentSpace p.1).injective
  have hcast : NormedSpace.fromTangentSpace p.1
      (mfderiv 𝓘(ℝ, Base × ℝ) 𝓘(ℝ, Base) Prod.fst p v) =
      (NormedSpace.fromTangentSpace p v).1 := by
    rw [show (Prod.fst : Base × ℝ → Base) =
      ContinuousLinearMap.fst ℝ Base ℝ from rfl]
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    rfl
  change (NormedSpace.fromTangentSpace p.1)
      ((NormedSpace.fromTangentSpace p.1).symm ((NormedSpace.fromTangentSpace p v).1)) = _
  rw [(NormedSpace.fromTangentSpace p.1).apply_symm_apply]
  exact hcast.symm

/-- In model coordinates, the off-diagonal soldering is exactly the
translational component of the existing homothety Cartan form. -/
theorem offDiagonalSoldering_eq_cartan_translation (κ : ℝ) (p : Base × ℝ)
    (v : TangentSpace 𝓘(ℝ, Base × ℝ) p) :
    offDiagonalSoldering p (baseTangentFromTotal p v) =
      ((InfoGeometry.Erlangen.SmoothCartanGeometry.homothetyCartanGeometry κ).omega p v).trans := by
  change offDiagonalSoldering p (baseTangentFromTotal p v) =
    (InfoGeometry.Erlangen.SmoothCartanGeometry.homothetyCartanOmega κ p v).trans
  rw [offDiagonalSoldering_apply,
    InfoGeometry.Erlangen.SmoothCartanGeometry.homothetyCartanOmega_apply]
  change Real.exp (-p.2) •
      NormedSpace.fromTangentSpace p.1
        ((NormedSpace.fromTangentSpace p.1).symm ((NormedSpace.fromTangentSpace p v).1)) =
    Real.exp (-p.2) • (NormedSpace.fromTangentSpace p v).1
  rw [(NormedSpace.fromTangentSpace p.1).apply_symm_apply]

end InfoGeometry.Canonical.HomothetyOffDiagonalSoldering

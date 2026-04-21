import InfoGeometry.Geometry.DualFlat
import InfoGeometry.Geometry.LegendreDuality
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.Vacuity

/-!
# InfoGeometry.Geometry.LegendreHessianInverse

Owner surface for the smooth part of the Souriau/Fisher/Fenchel inverse-metric
claim.

The informal statement says that, under Legendre duality, the Hessian of the
entropy potential in moment coordinates is the inverse of the Fisher/Hessian
metric in temperature coordinates.  This file does not prove an inverse-function
theorem.  Instead it records the exact local data needed after such an analytic
theorem has been supplied:

* a Massieu/Hessian geometry on the temperature side;
* a moment coordinate `q = dΦ β`;
* an entropy-gradient map `β(q)`;
* the Fisher Hessian `d(dΦ)_β`;
* the entropy Hessian `dβ_q`;
* the two chain-rule inverse laws.

The resulting theorem is therefore proof-carrying but honest: the hard
analytic existence/invertibility hypotheses are explicit fields, not hidden in
terminology.
-/

namespace InfoGeometry.Geometry

variable {Θ : Type _}
variable [NormedAddCommGroup Θ]
variable [NormedSpace ℝ Θ]

/-- Moment/covector coordinate space dual to the temperature carrier. -/
abbrev MomentCoord (Θ : Type _) [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] :=
  Θ →L[ℝ] ℝ

/--
Local Legendre Hessian-inverse context.

`massieu` owns the temperature-side potential `Φ`.
`entropyGradient` is the moment-side gradient/readout `∇S`, returning the
temperature coordinate.  The two Hessian fields are the local derivatives
whose composition laws express `Hess(S) = Hess(Φ)⁻¹`.
-/
@[rep_depth thermo]
structure LegendreHessianInverseContext (Θ : Type _)
    [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] where
  massieu : HessianGeometry Θ
  beta : Θ
  moment : MomentCoord Θ
  entropyGradient : MomentCoord Θ → Θ
  fisherHessian : Θ →L[ℝ] MomentCoord Θ
  entropyHessian : MomentCoord Θ →L[ℝ] Θ
  moment_eq_massieuGradient : moment = dualCoord massieu beta
  entropyGradient_at_moment : entropyGradient moment = beta
  fisherHessian_eq_massieuHessian : fisherHessian = hessian massieu beta
  entropyHessian_eq_gradientDerivative :
    entropyHessian = fderiv ℝ entropyGradient moment
  entropyHessian_comp_fisherHessian :
    entropyHessian.comp fisherHessian = ContinuousLinearMap.id ℝ Θ
  fisherHessian_comp_entropyHessian :
    fisherHessian.comp entropyHessian = ContinuousLinearMap.id ℝ (MomentCoord Θ)

namespace LegendreHessianInverseContext

variable (C : LegendreHessianInverseContext Θ)

/-- The moment coordinate is the Massieu gradient at `β`. -/
@[rep_depth thermo]
theorem moment_eq_gradient :
    C.moment = dualCoord C.massieu C.beta :=
  C.moment_eq_massieuGradient

/-- The entropy-gradient map returns the temperature coordinate at the contact moment. -/
@[rep_depth thermo]
theorem entropyGradient_contact :
    C.entropyGradient C.moment = C.beta :=
  C.entropyGradient_at_moment

/-- The Fisher side is the Hessian of the Massieu potential. -/
@[rep_depth thermo]
theorem fisherHessian_eq_hessianMassieu :
    C.fisherHessian = hessian C.massieu C.beta :=
  C.fisherHessian_eq_massieuHessian

/-- The entropy side is the derivative of the entropy-gradient map. -/
@[rep_depth thermo]
theorem entropyHessian_eq_derivEntropyGradient :
    C.entropyHessian = fderiv ℝ C.entropyGradient C.moment :=
  C.entropyHessian_eq_gradientDerivative

/--
Smooth Legendre inverse-metric theorem surface.

This is the precise local theorem shape for the prose statement
`Hess(S) = Fisher⁻¹`: the entropy Hessian and Fisher Hessian are two-sided
inverses as continuous linear maps.
-/
@[rep_depth thermo]
theorem entropy_hessian_eq_fisher_inverse :
    C.entropyHessian.comp C.fisherHessian = ContinuousLinearMap.id ℝ Θ
      ∧ C.fisherHessian.comp C.entropyHessian =
          ContinuousLinearMap.id ℝ (MomentCoord Θ) :=
  ⟨C.entropyHessian_comp_fisherHessian,
    C.fisherHessian_comp_entropyHessian⟩

/--
Expanded packet exposing the contact, Hessian identification, and inverse laws
in one theorem for theorem-factory retrieval.
-/
@[rep_depth thermo]
theorem legendre_hessian_inverse_packet :
    C.moment = dualCoord C.massieu C.beta
      ∧ C.entropyGradient C.moment = C.beta
      ∧ C.fisherHessian = hessian C.massieu C.beta
      ∧ C.entropyHessian = fderiv ℝ C.entropyGradient C.moment
      ∧ C.entropyHessian.comp C.fisherHessian = ContinuousLinearMap.id ℝ Θ
      ∧ C.fisherHessian.comp C.entropyHessian =
          ContinuousLinearMap.id ℝ (MomentCoord Θ) :=
  ⟨C.moment_eq_gradient,
    C.entropyGradient_contact,
    C.fisherHessian_eq_hessianMassieu,
    C.entropyHessian_eq_derivEntropyGradient,
    C.entropy_hessian_eq_fisher_inverse.1,
    C.entropy_hessian_eq_fisher_inverse.2⟩

attribute [terminal] legendre_hessian_inverse_packet

end LegendreHessianInverseContext

end InfoGeometry.Geometry

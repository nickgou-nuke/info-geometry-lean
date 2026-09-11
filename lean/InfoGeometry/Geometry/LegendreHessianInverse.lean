import InfoGeometry.Geometry.DualFlat
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-! ## Constructive local inverse from a continuous-linear equivalence -/

/--
Dimension-agnostic local Legendre inverse data where the Hessian inverse is not
an arbitrary pair of linear maps with inverse-law hypotheses.

The Fisher Hessian is supplied as a continuous-linear equivalence and the
entropy Hessian is its inverse.  Thus the two-sided inverse laws are proved
constructively from the equivalence, while the genuinely analytic obligations
left to the concrete smooth model are the Hessian identification and the
derivative identification of the entropy-gradient map.
-/
@[rep_depth thermo]
structure LegendreContinuousLinearEquivInverseData (Θ : Type _)
    [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] where
  massieu : HessianGeometry Θ
  beta : Θ
  entropyGradient : MomentCoord Θ → Θ
  fisherEquiv : Θ ≃L[ℝ] MomentCoord Θ
  entropyGradient_at_moment :
    entropyGradient (dualCoord massieu beta) = beta
  fisherEquiv_eq_massieuHessian :
    (fisherEquiv : Θ →L[ℝ] MomentCoord Θ) = hessian massieu beta
  entropyGradient_derivative_eq_inverse :
    fderiv ℝ entropyGradient (dualCoord massieu beta) =
      (fisherEquiv.symm : MomentCoord Θ →L[ℝ] Θ)

namespace LegendreContinuousLinearEquivInverseData

variable (D : LegendreContinuousLinearEquivInverseData Θ)

/-- The moment coordinate is constructively the Massieu gradient at `β`. -/
@[rep_depth thermo]
noncomputable def moment : MomentCoord Θ :=
  dualCoord D.massieu D.beta

/-- Fisher Hessian as the forward continuous-linear equivalence. -/
@[rep_depth thermo]
noncomputable def fisherHessian : Θ →L[ℝ] MomentCoord Θ :=
  D.fisherEquiv

/-- Entropy Hessian as the inverse continuous-linear equivalence. -/
@[rep_depth thermo]
noncomputable def entropyHessian : MomentCoord Θ →L[ℝ] Θ :=
  D.fisherEquiv.symm

/-- The inverse entropy Hessian composed with Fisher is identity. -/
@[rep_depth thermo]
theorem entropyHessian_comp_fisherHessian :
    D.entropyHessian.comp D.fisherHessian =
      ContinuousLinearMap.id ℝ Θ := by
  ext x
  simp [entropyHessian, fisherHessian]

/-- Fisher composed with the inverse entropy Hessian is identity. -/
@[rep_depth thermo]
theorem fisherHessian_comp_entropyHessian :
    D.fisherHessian.comp D.entropyHessian =
      ContinuousLinearMap.id ℝ (MomentCoord Θ) := by
  ext q
  simp [entropyHessian, fisherHessian]

/--
Build the existing Legendre inverse context from explicit continuous-linear
equivalence data.  The two inverse laws are no longer fields: they are proved
from `fisherEquiv` and `fisherEquiv.symm`.
-/
@[rep_depth thermo]
noncomputable def toLegendreHessianInverseContext :
    LegendreHessianInverseContext Θ where
  massieu := D.massieu
  beta := D.beta
  moment := D.moment
  entropyGradient := D.entropyGradient
  fisherHessian := D.fisherHessian
  entropyHessian := D.entropyHessian
  moment_eq_massieuGradient := rfl
  entropyGradient_at_moment := D.entropyGradient_at_moment
  fisherHessian_eq_massieuHessian := D.fisherEquiv_eq_massieuHessian
  entropyHessian_eq_gradientDerivative := by
    exact D.entropyGradient_derivative_eq_inverse.symm
  entropyHessian_comp_fisherHessian :=
    D.entropyHessian_comp_fisherHessian
  fisherHessian_comp_entropyHessian :=
    D.fisherHessian_comp_entropyHessian

/--
Constructive inverse-Hessian packet from a continuous-linear equivalence.

This is the dimension-agnostic replacement for separately assuming the two
inverse laws in the Legendre context.
-/
@[rep_depth thermo]
theorem constructive_legendre_hessian_inverse_packet :
    D.toLegendreHessianInverseContext.moment =
        dualCoord D.massieu D.beta
      ∧ D.entropyGradient D.toLegendreHessianInverseContext.moment = D.beta
      ∧ D.toLegendreHessianInverseContext.fisherHessian =
        hessian D.massieu D.beta
      ∧ D.toLegendreHessianInverseContext.entropyHessian =
        fderiv ℝ D.entropyGradient D.toLegendreHessianInverseContext.moment
      ∧ D.toLegendreHessianInverseContext.entropyHessian.comp
          D.toLegendreHessianInverseContext.fisherHessian =
        ContinuousLinearMap.id ℝ Θ
      ∧ D.toLegendreHessianInverseContext.fisherHessian.comp
          D.toLegendreHessianInverseContext.entropyHessian =
        ContinuousLinearMap.id ℝ (MomentCoord Θ) := by
  exact D.toLegendreHessianInverseContext.legendre_hessian_inverse_packet

attribute [terminal] constructive_legendre_hessian_inverse_packet

end LegendreContinuousLinearEquivInverseData

end InfoGeometry.Geometry

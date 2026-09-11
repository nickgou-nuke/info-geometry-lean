import InfoGeometry.GrandCanonical.Core
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ModularKLDivergenceBridge
import InfoGeometry.Canonical.SinkhornFoundation
import InfoGeometry.Canonical.RelativePotentialScalarBridge
import InfoGeometry.ExponentialFamily.Gaussian
import InfoGeometry.Projective.Orthant
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.GrandCanonicalGaussianScaleShape

Canonical bridge for the grand-canonical unnormalized Gaussian lane:
- strict-positive generalized-KL decomposition into projective shape and radial scale;
- RN/Kähler potential readout as negative log relative-volume change on the
  self-dual-cone transport lane.

No new ontology is introduced here; this module packages existing owner
surfaces into a single repo-native formula surface.
-/

namespace InfoGeometry.Canonical.GrandCanonicalGaussianScaleShape

open scoped BigOperators
open InfoGeometry.ExponentialFamily.Gaussian
open InfoGeometry.GrandCanonical
open InfoGeometry.PositiveMeasure
open InfoGeometry.Canonical.ModularKLDivergenceBridge
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.RelativePotentialScalarBridge

section GrandCanonicalGaussian

variable {α E : Type*}
variable [Fintype α] [Nonempty α]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Parameter point on the grand-canonical unnormalized Gaussian manifold. -/
@[rep_depth projective]
structure GrandCanonicalGaussianPoint where
  eta : E
  beta : ℝ
  chemicalPotential : ℝ

/--
Coordinate-free Gaussian energy on the carrier `α`, induced by observable
embedding `obs` and Gaussian Hessian operator `sigma`.
-/
@[rep_depth projective]
noncomputable def gaussianEnergy
    (G : GaussianFamily E)
    (obs : α → E)
    (eta : E)
    (x : α) : ℝ :=
  (1 / 2 : ℝ) * inner ℝ (obs x - eta) (G.sigma (obs x - eta))

/--
Grand-canonical parameter package from Gaussian energy and a number observable.
-/
@[rep_depth projective]
noncomputable def gaussianGrandCanonicalParams
    (G : GaussianFamily E)
    (obs : α → E)
    (numberObs : α → ℝ)
    (eta : E) :
    GrandCanonicalTwoParam α where
  energy := gaussianEnergy (α := α) (E := E) G obs eta
  number := numberObs

/--
Unnormalized grand-canonical Gaussian state:
`exp(-β (E_η - μ N))` as a strictly positive measure.
-/
@[rep_depth projective]
noncomputable def unnormalizedGrandCanonicalGaussian
    (G : GaussianFamily E)
    (obs : α → E)
    (numberObs : α → ℝ)
    (p : GrandCanonicalGaussianPoint (E := E)) :
    PositiveMeasure α ℝ where
  mass x :=
    Real.exp
      (-p.beta
        * shiftedEnergy
            (gaussianGrandCanonicalParams
              (α := α) (E := E) G obs numberObs p.eta)
            p.chemicalPotential x)
  pos _ := Real.exp_pos _

/-- Projective/IS-style shape term in the strict-positive generalized-KL split. -/
@[rep_depth projective]
noncomputable def generalizedKL_ISShapeTerm
    (μ ν : PositiveMeasure α ℝ) : ℝ :=
  Z (α := α) (R := ℝ) μ
    * generalizedKL (α := α)
        (normalize (α := α) (R := ℝ) μ)
        (normalize (α := α) (R := ℝ) ν)

/-- Radial scale term in the strict-positive generalized-KL split. -/
@[rep_depth projective]
noncomputable def generalizedKL_scaleTerm
    (μ ν : PositiveMeasure α ℝ) : ℝ :=
  gklTerm (Z (α := α) (R := ℝ) μ) (Z (α := α) (R := ℝ) ν)

/--
Canonical formula on the strict-positive cone:
`KL = IS-shape + scale`.
-/
@[rep_depth projective]
theorem generalizedKL_eq_ISShape_add_scaleTerm
    (μ ν : PositiveMeasure α ℝ) :
    generalizedKL (α := α) μ ν
      = generalizedKL_ISShapeTerm (α := α) μ ν
        + generalizedKL_scaleTerm (α := α) μ ν := by
  simpa [generalizedKL_ISShapeTerm, generalizedKL_scaleTerm] using
    (InfoGeometry.Canonical.ModularKLDivergenceBridge.generalizedKL_scale_shape_split
      (α := α) μ ν)

/--
Grand-canonical unnormalized Gaussian specialization of the same formula.
-/
@[rep_depth projective]
theorem generalizedKL_unnormalizedGrandCanonicalGaussian_eq_ISShape_add_scaleTerm
    (G : GaussianFamily E)
    (obs : α → E)
    (numberObs : α → ℝ)
    (p q : GrandCanonicalGaussianPoint (E := E)) :
    generalizedKL (α := α)
        (unnormalizedGrandCanonicalGaussian (α := α) (E := E) G obs numberObs p)
        (unnormalizedGrandCanonicalGaussian (α := α) (E := E) G obs numberObs q)
      =
    generalizedKL_ISShapeTerm (α := α)
        (unnormalizedGrandCanonicalGaussian (α := α) (E := E) G obs numberObs p)
        (unnormalizedGrandCanonicalGaussian (α := α) (E := E) G obs numberObs q)
      +
    generalizedKL_scaleTerm (α := α)
        (unnormalizedGrandCanonicalGaussian (α := α) (E := E) G obs numberObs p)
        (unnormalizedGrandCanonicalGaussian (α := α) (E := E) G obs numberObs q) := by
  exact generalizedKL_eq_ISShape_add_scaleTerm
    (α := α)
    (μ := unnormalizedGrandCanonicalGaussian (α := α) (E := E) G obs numberObs p)
    (ν := unnormalizedGrandCanonicalGaussian (α := α) (E := E) G obs numberObs q)

end GrandCanonicalGaussian

section SelfDualConeKahler

variable (n : Nat)

/--
Canonical self-dual cone for the Sinkhorn matrix lane (`Fin n × Fin n` orthant).
-/
@[rep_depth projective]
noncomputable abbrev sinkhornSelfDualCone :
    InfoGeometry.Projective.SelfDualCone (EuclideanSpace ℝ (Fin n × Fin n)) :=
  InfoGeometry.Projective.positiveOrthant (α := Fin n × Fin n)

variable {n}

/--
RN/Kähler potential equals the scalar modular potential of relative-volume
change on the strict-positive self-dual-cone lane.
-/
@[rep_depth operator]
theorem kahlerPotentialRN_eq_scalarModularPotential_relativeVolumeChangeRN
    (M : SinkhornMatrix n) :
    kahlerPotentialRN n M =
      scalarModularPotential
        (relativeVolumeChangeRN n M)
        (by
          unfold relativeVolumeChangeRN
          exact Real.exp_pos _) := by
  simpa using
    (InfoGeometry.Canonical.MoE.kahlerPotentialRN_eq_scalarModularPotential_relativeVolumeChangeRN
      (n := n) M)

/--
Equivalent logarithmic form:
the RN/Kähler potential is `-log` of the relative-volume change.
-/
@[rep_depth operator]
theorem kahlerPotentialRN_eq_neg_log_relativeVolumeChangeRN
    (M : SinkhornMatrix n) :
    kahlerPotentialRN n M = -Real.log (relativeVolumeChangeRN n M) := by
  rw [kahlerPotentialRN_eq_scalarModularPotential_relativeVolumeChangeRN (n := n) M]
  rw [scalarModularPotential_eq_neg_log]

end SelfDualConeKahler

end InfoGeometry.Canonical.GrandCanonicalGaussianScaleShape

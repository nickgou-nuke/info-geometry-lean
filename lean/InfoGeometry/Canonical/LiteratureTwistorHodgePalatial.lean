import InfoGeometry.Canonical.ChiralHodgeDecomposition
import InfoGeometry.Canonical.TwistorOperatorialIncidence
import InfoGeometry.Canonical.WeylTransport
import InfoGeometry.Twistor.Incidence
import InfoGeometry.Meta.Architecture

/-!
# Literature Twistor-Hodge-Palatial Bridge

This module records the literature-facing surface connecting:

* the four-dimensional twistor/Hodge split into self-dual and anti-self-dual
  two-form sectors,
* Penrose contour-integral readouts as an abstract line-integral/holonomy
  interface,
* Penrose's palatial-twistor proposal as a noncommutative operator algebra
  extending holomorphic twistor functions by twistor differentiation operators.

The file is intentionally conservative.  It does not identify the repo's graph
Hodge operator with smooth exterior-calculus Hodge star, and it does not claim a
full analytic Penrose transform.  Those analytic facts enter only as explicit
witness fields.
-/

namespace InfoGeometry.Canonical.LiteratureTwistorHodgePalatial

/-! ## Hodge self-dual / anti-self-dual split -/

/--
Abstract Hodge-star split for the two-form sector used in four-dimensional
twistor theory.

In the literature this is the `Λ² = Λ²₊ ⊕ Λ²₋` decomposition induced by the
Hodge star and depending only on the conformal class.  Here it is represented as
a proof-carrying interface, not as a complete exterior-calculus development.
-/
@[rep_depth krein]
structure HodgeSelfDualSplit (Ω : Type*) [Neg Ω] where
  hodgeStar : Ω → Ω
  selfDual : Ω → Prop
  antiSelfDual : Ω → Prop
  hodge_selfDual : ∀ ω, selfDual ω → hodgeStar ω = ω
  hodge_antiSelfDual : ∀ ω, antiSelfDual ω → hodgeStar ω = -ω

namespace HodgeSelfDualSplit

variable {Ω : Type*} [Neg Ω] (H : HodgeSelfDualSplit Ω)

/-- Self-dual forms are fixed by the supplied Hodge star. -/
@[rep_depth krein]
theorem hodgeStar_eq_self_of_mem (ω : Ω) (hω : H.selfDual ω) :
    H.hodgeStar ω = ω :=
  H.hodge_selfDual ω hω

/-- Anti-self-dual forms are negated by the supplied Hodge star. -/
@[rep_depth krein]
theorem hodgeStar_eq_neg_of_anti_mem (ω : Ω) (hω : H.antiSelfDual ω) :
    H.hodgeStar ω = -ω :=
  H.hodge_antiSelfDual ω hω

end HodgeSelfDualSplit

/-! ## Penrose contour readout as line-integral/holonomy data -/

/--
Penrose-transform contour data in the same abstract style as the repo's Weyl
transport layer.

The contour integral itself is carried by `integrator`; the mathematical claim
that this readout solves or represents the target field is the field
`contourReadout_eq_field`.
-/
@[rep_depth transport]
structure PenroseContourIntegralData
    (I Tw A S Field : Type*) where
  contour : WeylTrajectory I Tw
  integrator : WeylLineIntegrator I A S
  readout : WeylHolonomyMap S Field
  integrand : Tw → A
  field : Field
  contourReadout_eq_field :
    readout.toHolonomy
      (integrator.integrate (fun i => integrand (contour.point i))) =
        field

namespace PenroseContourIntegralData

variable {I Tw A S Field : Type*}
variable (P : PenroseContourIntegralData I Tw A S Field)

/-- The contour-holonomy readout is the represented Penrose field. -/
@[rep_depth transport]
theorem contourReadout_eq :
    P.readout.toHolonomy
      (P.integrator.integrate (fun i => P.integrand (P.contour.point i))) =
        P.field :=
  P.contourReadout_eq_field

end PenroseContourIntegralData

/--
Combined Penrose-Hodge package: a contour representative together with an
explicit choice of SD/ASD Hodge sector for the field it represents.
-/
@[rep_depth transport]
structure PenroseHodgeIntegralData
    (I Tw A S Field Ω : Type*) [Neg Ω] where
  hodge : HodgeSelfDualSplit Ω
  contour : PenroseContourIntegralData I Tw A S Field
  fieldToForm : Field → Ω
  representedForm : Ω
  representedForm_eq : representedForm = fieldToForm contour.field
  representedForm_selfDual_or_antiSelfDual :
    hodge.selfDual representedForm ∨ hodge.antiSelfDual representedForm

namespace PenroseHodgeIntegralData

variable {I Tw A S Field Ω : Type*} [Neg Ω]
variable (P : PenroseHodgeIntegralData I Tw A S Field Ω)

/-- The Penrose contour readout still controls the underlying field. -/
@[rep_depth transport]
theorem contourReadout_eq_field :
    P.contour.readout.toHolonomy
      (P.contour.integrator.integrate
        (fun i => P.contour.integrand (P.contour.contour.point i))) =
        P.contour.field :=
  P.contour.contourReadout_eq

/-- The represented form lies in one of the two Hodge sectors by hypothesis. -/
@[rep_depth krein]
theorem representedForm_mem_hodge_sector :
    P.hodge.selfDual P.representedForm ∨ P.hodge.antiSelfDual P.representedForm :=
  P.representedForm_selfDual_or_antiSelfDual

end PenroseHodgeIntegralData

/-! ## Palatial twistor operator algebra -/

/--
Noncommutative palatial-twistor operator algebra interface.

Penrose's palatial proposal enlarges holomorphic twistor functions by operators
of twistor differentiation.  This structure records only the algebraic
Heisenberg-style commutator surface needed by downstream Lean bridges.
-/
@[rep_depth operator]
structure PalatialTwistorOperatorAlgebra (Op Scalar : Type*) where
  coordinate : Op
  derivative : Op
  commutator : Op → Op → Op
  scalarEmbed : Scalar → Op
  heisenbergScalar : Scalar
  coordinate_derivative_commutator :
    commutator coordinate derivative = scalarEmbed heisenbergScalar

namespace PalatialTwistorOperatorAlgebra

variable {Op Scalar : Type*}
variable (A : PalatialTwistorOperatorAlgebra Op Scalar)

/-- Projection of the palatial Heisenberg commutator law. -/
@[rep_depth operator]
theorem coordinate_derivative_commutator_eq :
    A.commutator A.coordinate A.derivative = A.scalarEmbed A.heisenbergScalar :=
  A.coordinate_derivative_commutator

end PalatialTwistorOperatorAlgebra

/--
Bridge package from palatial noncommutative twistors to the Penrose-Hodge
contour lane.

This is the legitimate place to assert that a particular operator realization
respects the contour/Hodge field.  The compatibility is an explicit hypothesis,
not a theorem derived from graph proximity or prose.
-/
@[rep_depth transport]
structure PalatialPenroseHodgeBridge
    (I Tw A S Field Ω Op Scalar : Type*) [Neg Ω] where
  penroseHodge : PenroseHodgeIntegralData I Tw A S Field Ω
  palatial : PalatialTwistorOperatorAlgebra Op Scalar
  operatorRealization : Op → Field
  contourOperator : Op
  contourOperator_realizes_field :
    operatorRealization contourOperator = penroseHodge.contour.field

namespace PalatialPenroseHodgeBridge

variable {I Tw A S Field Ω Op Scalar : Type*} [Neg Ω]
variable (B : PalatialPenroseHodgeBridge I Tw A S Field Ω Op Scalar)

/-- The chosen palatial operator realizes the field read by the Penrose contour. -/
@[rep_depth transport]
theorem operatorRealization_eq_contourField :
    B.operatorRealization B.contourOperator = B.penroseHodge.contour.field :=
  B.contourOperator_realizes_field

/-- The same field is the contour-holonomy readout. -/
@[rep_depth transport]
theorem contourReadout_eq_operatorRealization :
    B.penroseHodge.contour.readout.toHolonomy
      (B.penroseHodge.contour.integrator.integrate
        (fun i =>
          B.penroseHodge.contour.integrand
            (B.penroseHodge.contour.contour.point i))) =
        B.operatorRealization B.contourOperator := by
  rw [B.penroseHodge.contourReadout_eq_field, B.contourOperator_realizes_field]

/-- The bridge inherits the palatial noncommutative commutator law. -/
@[rep_depth operator]
theorem palatial_commutator :
    B.palatial.commutator B.palatial.coordinate B.palatial.derivative =
      B.palatial.scalarEmbed B.palatial.heisenbergScalar :=
  B.palatial.coordinate_derivative_commutator_eq

end PalatialPenroseHodgeBridge

/-! ## Repo-native chiral Hodge sanity projections -/

open InfoGeometry.Canonical.ChiralHodgeDecomposition

section RootChiralHodge

open scoped InnerProductSpace

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
Repo-owned sanity check: the root positive chiral Hodge loop is exactly the
positive spectral projector.  This is the operator/Krein Hodge lane, not the
smooth twistor exterior-calculus Hodge star.
-/
@[rep_depth krein]
theorem root_positive_chiral_hodge_loop_is_projector :
    rootChiralLaplacianPlus (E := E) =
      spectralChiralPlusProjector (E := E) :=
  rootChiralLaplacianPlus_eq_spectralChiralPlusProjector (E := E)

/--
Repo-owned sanity check: the root negative chiral Hodge loop is exactly the
negative spectral projector.
-/
@[rep_depth krein]
theorem root_negative_chiral_hodge_loop_is_projector :
    rootChiralLaplacianMinus (E := E) =
      spectralChiralMinusProjector (E := E) :=
  rootChiralLaplacianMinus_eq_spectralChiralMinusProjector (E := E)

end RootChiralHodge

end InfoGeometry.Canonical.LiteratureTwistorHodgePalatial

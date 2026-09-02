import InfoGeometry.Lie.CanonicalZornOperatorDerivationLane
import InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
import InfoGeometry.OperatorAlgebra.DerivationVectorCalculus

/-!
# Canonical split-octonion derivation forms on the operator algebra

This file specializes the generic derivation differential complex to the
faithful action

`Der(O_s) -> Der(End_R(O_s))`,

where every canonical Zorn derivation acts on an operator by commutator.  The
coefficient algebra is therefore the associative endomorphism algebra, not a
Zorn construction with noncommutative coefficients.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CanonicalZornDerivationDifferentialForms

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornOperatorDerivationLane
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.DerivationVectorCalculus

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ
abbrev ZornDer := canonicalZornDerivations
abbrev Lane := canonicalZornOperatorDerivationLane

/-- Canonical operator-valued one-forms on the split-octonion derivation Lie
algebra. -/
abbrev OperatorOneForm := OneForm Lane

/-- Canonical alternating operator-valued two-forms. -/
abbrev OperatorTwoForm := TwoForm Lane

/-- Canonical degree-three cochain target. -/
abbrev OperatorThreeCochain := ThreeCochain Lane

/-- On zero-forms, the derivation differential is the operator commutator. -/
@[simp] theorem exteriorDerivativeZero_apply
    (T : EndCZ) (D : ZornDer) :
    DerivationDifferentialForms.exteriorDerivativeZero Lane T D =
      D.1 * T - T * D.1 :=
  rfl

/-- Explicit degree-one Chevalley--Eilenberg differential in operator
commutator coordinates. -/
theorem exteriorDerivativeOne_apply
    (ω : OperatorOneForm) (D E : ZornDer) :
    DerivationDifferentialForms.exteriorDerivativeOne Lane ω D E =
      (D.1 * ω E - ω E * D.1) -
        (E.1 * ω D - ω D * E.1) -
          ω ⁅D, E⁆ := by
  simpa using
    (DerivationDifferentialForms.exteriorDerivativeOne_apply Lane ω D E)

/-- The split-octonion operator differential squares to zero on zero-forms. -/
theorem exteriorDerivativeOne_exteriorDerivativeZero
    (T : EndCZ) :
    DerivationDifferentialForms.exteriorDerivativeOne Lane
        (DerivationDifferentialForms.exteriorDerivativeZero Lane T) = 0 :=
  DerivationDifferentialForms.exteriorDerivativeOne_exteriorDerivativeZero Lane T

/-- Curvature of a canonical operator-valued connection, in explicit
commutator coordinates. -/
theorem connectionCurvature_apply
    (Γ : OperatorOneForm) (D E : ZornDer) :
    DerivationDifferentialForms.connectionCurvature Lane Γ D E =
      (D.1 * Γ E - Γ E * D.1) -
        (E.1 * Γ D - Γ D * E.1) -
          Γ ⁅D, E⁆ +
            (Γ D * Γ E - Γ E * Γ D) := by
  simpa using
    (DerivationDifferentialForms.connectionCurvature_apply Lane Γ D E)

/-- Curvature is exactly the defect in the represented Lie bracket of the
connection-corrected derivations. -/
theorem covariantDerivative_commutator
    (Γ : OperatorOneForm) (D E : ZornDer) (T : EndCZ) :
    DerivationDifferentialForms.covariantDerivative Lane Γ D
          (DerivationDifferentialForms.covariantDerivative Lane Γ E T) -
        DerivationDifferentialForms.covariantDerivative Lane Γ E
          (DerivationDifferentialForms.covariantDerivative Lane Γ D T) -
        DerivationDifferentialForms.covariantDerivative Lane Γ ⁅D, E⁆ T =
      DerivationDifferentialForms.connectionCurvature Lane Γ D E * T -
        T * DerivationDifferentialForms.connectionCurvature Lane Γ D E :=
  DerivationDifferentialForms.covariantDerivative_commutator Lane Γ D E T

/-- Canonical operator curvature satisfies the covariant Bianchi identity. -/
theorem connectionCurvature_bianchi
    (Γ : OperatorOneForm) (D E F : ZornDer) :
    DerivationDifferentialForms.covariantExteriorDerivativeTwo Lane Γ
      (DerivationDifferentialForms.connectionCurvature Lane Γ) D E F = 0 :=
  DerivationDifferentialForms.connectionCurvature_bianchi Lane Γ D E F

/-- A flat canonical connection obeying the Maurer--Cartan equation has no
commutator defect. -/
theorem covariantDerivative_commutator_of_maurerCartan
    (Γ : OperatorOneForm)
    (hΓ : DerivationDifferentialForms.SatisfiesMaurerCartan Lane Γ)
    (D E : ZornDer) (T : EndCZ) :
    DerivationDifferentialForms.covariantDerivative Lane Γ D
          (DerivationDifferentialForms.covariantDerivative Lane Γ E T) -
        DerivationDifferentialForms.covariantDerivative Lane Γ E
          (DerivationDifferentialForms.covariantDerivative Lane Γ D T) -
        DerivationDifferentialForms.covariantDerivative Lane Γ ⁅D, E⁆ T = 0 :=
  DerivationDifferentialForms.covariantDerivative_commutator_of_maurerCartan
    Lane Γ hΓ D E T

/-- Three canonical split-octonion derivations form the operator differential
frame used by the bracket-corrected vector-calculus readout. -/
abbrev OperatorDerivationFrame3 := DerivationFrame3 Lane

/-- The curl of an operator gradient is the cyclic split-octonion derivation
bracket action. -/
theorem curl_gradient_eq_bracketAction
    (frame : OperatorDerivationFrame3) (T : EndCZ) :
    DerivationVectorCalculus.curl Lane frame
        (DerivationVectorCalculus.gradient Lane frame T) =
      fun i =>
        if i = (0 : Fin 3) then
          Lane.operatorAction ⁅frame 1, frame 2⁆ T
        else if i = (1 : Fin 3) then
          Lane.operatorAction ⁅frame 2, frame 0⁆ T
        else
          Lane.operatorAction ⁅frame 0, frame 1⁆ T :=
  DerivationVectorCalculus.curl_gradient_eq_bracketAction Lane frame T

end InfoGeometry.OperatorAlgebra.CanonicalZornDerivationDifferentialForms

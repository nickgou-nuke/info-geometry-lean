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
abbrev ActionLane := canonicalZornOperatorActionLane

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
    (ω : OperatorOneForm) (D E : Lane.L) :
    DerivationDifferentialForms.exteriorDerivativeOne Lane ω D E =
      (D.1 * ω E - ω E * D.1) -
        (E.1 * ω D - ω D * E.1) -
          ω ⁅(D : Lane.L), (E : Lane.L)⁆ := by
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
    (Γ : OperatorOneForm) (D E : Lane.L) :
    DerivationDifferentialForms.connectionCurvature Lane Γ D E =
      (D.1 * Γ E - Γ E * D.1) -
        (E.1 * Γ D - Γ D * E.1) -
          Γ ⁅(D : Lane.L), (E : Lane.L)⁆ +
            (Γ D * Γ E - Γ E * Γ D) := by
  simpa using
    (DerivationDifferentialForms.connectionCurvature_apply Lane Γ D E)

/-- Curvature is exactly the defect in the represented Lie bracket of the
connection-corrected derivations. -/
theorem covariantDerivative_commutator
    (Γ : OperatorOneForm) (D E : Lane.L) (T : EndCZ) :
    DerivationDifferentialForms.covariantDerivative Lane Γ D
          (DerivationDifferentialForms.covariantDerivative Lane Γ E T) -
        DerivationDifferentialForms.covariantDerivative Lane Γ E
          (DerivationDifferentialForms.covariantDerivative Lane Γ D T) -
        DerivationDifferentialForms.covariantDerivative Lane Γ
          ⁅(D : Lane.L), (E : Lane.L)⁆ T =
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
    (D E : Lane.L) (T : EndCZ) :
    DerivationDifferentialForms.covariantDerivative Lane Γ D
          (DerivationDifferentialForms.covariantDerivative Lane Γ E T) -
        DerivationDifferentialForms.covariantDerivative Lane Γ E
          (DerivationDifferentialForms.covariantDerivative Lane Γ D T) -
        DerivationDifferentialForms.covariantDerivative Lane Γ
          ⁅(D : Lane.L), (E : Lane.L)⁆ T = 0 :=
  DerivationDifferentialForms.covariantDerivative_commutator_of_maurerCartan
    Lane Γ hΓ D E T

/-! ## Canonical Maurer--Cartan connection -/

/-- The left Maurer--Cartan sign convention on the adjoint operator module. -/
def canonicalMaurerCartanForm : OperatorOneForm where
  toFun D := -D.1
  map_add' D E := by
    change -(D.1 + E.1) = -D.1 + -E.1
    exact neg_add D.1 E.1
  map_smul' r D := by
    change -(r • D.1) = r • (-D.1)
    module

@[simp] theorem canonicalMaurerCartanForm_apply (D : ZornDer) :
    canonicalMaurerCartanForm D = -D.1 :=
  rfl

/-- The canonical Maurer--Cartan form is flat. -/
theorem canonicalMaurerCartanForm_curvature :
    DerivationDifferentialForms.connectionCurvature
      Lane canonicalMaurerCartanForm = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro D
  apply LinearMap.ext
  intro E
  change DerivationDifferentialForms.connectionCurvature
      Lane canonicalMaurerCartanForm D E = 0
  rw [connectionCurvature_apply]
  simp only [canonicalMaurerCartanForm_apply]
  have hbr : (⁅D, E⁆ : Lane.L).1 = D.1 * E.1 - E.1 * D.1 := rfl
  rw [hbr]
  noncomm_ring

/-- The canonical form satisfies the Maurer--Cartan predicate. -/
theorem canonicalMaurerCartanForm_satisfies :
    DerivationDifferentialForms.SatisfiesMaurerCartan
      Lane canonicalMaurerCartanForm :=
  canonicalMaurerCartanForm_curvature

@[simp] theorem canonicalMaurerCartan_covariantDerivative
    (D : ZornDer) (T : EndCZ) :
    DerivationDifferentialForms.covariantDerivative
      Lane canonicalMaurerCartanForm D T = 0 := by
  change
    (D.1 * T - T * D.1) + (-D.1) * T - T * (-D.1) = 0
  noncomm_ring

/-- Three canonical split-octonion derivations form the operator differential
frame used by the bracket-corrected vector-calculus readout. -/
abbrev OperatorDerivationFrame3 := DerivationFrame3 ActionLane

/-- The curl of an operator gradient is the cyclic split-octonion derivation
bracket action. -/
theorem curl_gradient_eq_bracketAction
    (frame : OperatorDerivationFrame3) (T : EndCZ) :
    DerivationVectorCalculus.curl ActionLane frame
        (DerivationVectorCalculus.gradient ActionLane frame T) =
      fun i =>
        if i = (0 : Fin 3) then
          ActionLane.operatorAction ⁅frame 1, frame 2⁆ T
        else if i = (1 : Fin 3) then
          ActionLane.operatorAction ⁅frame 2, frame 0⁆ T
        else
          ActionLane.operatorAction ⁅frame 0, frame 1⁆ T :=
  DerivationVectorCalculus.curl_gradient_eq_bracketAction ActionLane frame T

end InfoGeometry.OperatorAlgebra.CanonicalZornDerivationDifferentialForms

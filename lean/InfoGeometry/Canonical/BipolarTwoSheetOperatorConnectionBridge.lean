import InfoGeometry.Canonical.BipolarTwoSheetParabolicCausalBoundaryBridge
import InfoGeometry.Analysis.BipolarPlanarHodgePair
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra
import InfoGeometry.Information.ModularSurprisalDerivationBridge
import InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms
import Mathlib.Tactic

/-!
# Two-sheet bipolar operator connection

This file formalizes the finite operator-connection layer suggested by the
bipolar/two-sheet construction.  It deliberately separates three levels:

* the tangent carrier is the real two-coordinate plane `(dη,dθ)`;
* an operator-valued one-form assigns fixed algebra generators to those two
  directions;
* its algebraic self-wedge is exactly the commutator curvature term.

For the canonical Pauli Cartan realization

`Kboost = σ3/2`, `Kcirc = i σ3/2`,

the two generators commute.  Hence the commutator contribution to curvature
vanishes, while their adjoint actions on the two parabolic sheet generators
`σPlus, σMinus` carry opposite weights.

This is a finite constant-coefficient connection statement.  No exterior
derivative of a nonconstant form, Maurer--Cartan theorem, gauge bundle, BKM
metric identification, or metriplectic dynamics is inferred here.  Those are
separate owners and require their own hypotheses.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge

open InfoGeometry.Analysis.BipolarPlanarHodgePair
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Physics.ChiralCausalCone

abbrev Tangent2 := PlaneCovector
abbrev M2C := InfoGeometry.Physics.ChiralCausalCone.M2C

/-- Coordinate tangent in the logarithmic radial direction. -/
def etaTangent : Tangent2 := ![1, 0]

/-- Coordinate tangent in the angular direction. -/
def thetaTangent : Tangent2 := ![0, 1]

/-- Constant-coefficient operator-valued one-form
`A(v) = v_η Kη + v_θ Kθ`. -/
def operatorConnection (Kη Kθ : M2C) : Op1Form ℝ Tangent2 M2C where
  toFun v := v 0 • Kη + v 1 • Kθ
  map_add' u v := by
    ext i j
    simp [Matrix.add_apply, add_smul]
    ring
  map_smul' c v := by
    ext i j
    simp [Matrix.add_apply, mul_smul]
    ring

@[simp] theorem operatorConnection_eta (Kη Kθ : M2C) :
    operatorConnection Kη Kθ etaTangent = Kη := by
  ext i j
  simp [operatorConnection, etaTangent]

@[simp] theorem operatorConnection_theta (Kη Kθ : M2C) :
    operatorConnection Kη Kθ thetaTangent = Kθ := by
  ext i j
  simp [operatorConnection, thetaTangent]

/-- The coordinate self-wedge is exactly the commutator of the two connection
coefficients. -/
theorem wedge_connection_eta_theta (Kη Kθ : M2C) :
    wedge (operatorConnection Kη Kθ) (operatorConnection Kη Kθ)
        etaTangent thetaTangent =
      Kη * Kθ - Kθ * Kη := by
  rw [wedge_apply, operatorConnection_eta, operatorConnection_theta]

/-- Canonical noncompact Cartan generator. -/
def Kboost : M2C := (1 / 2 : ℂ) • σ3c

/-- Canonical compact Cartan generator. -/
def Kcirc : M2C := (Complex.I / 2 : ℂ) • σ3c

/-- The two canonical Cartan connection coefficients commute. -/
theorem Kboost_Kcirc_commute :
    Kboost * Kcirc - Kcirc * Kboost = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Kboost, Kcirc, σ3c, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Therefore the commutator curvature coefficient of the canonical connection
vanishes in the `(η,θ)` coordinate pair. -/
theorem canonical_connection_wedge_eta_theta_zero :
    wedge (operatorConnection Kboost Kcirc) (operatorConnection Kboost Kcirc)
        etaTangent thetaTangent = 0 := by
  rw [wedge_connection_eta_theta, Kboost_Kcirc_commute]

/-- The boost Cartan generator has weight `+1` on the plus parabolic sheet. -/
theorem Kboost_comm_sigmaPlus :
    Kboost * σPlus - σPlus * Kboost = σPlus := by
  simpa [Kboost, smul_sub, smul_smul] using
    congrArg (fun X : M2C => (1 / 2 : ℂ) • X) comm_σ3_σPlus

/-- The boost Cartan generator has weight `-1` on the minus parabolic sheet. -/
theorem Kboost_comm_sigmaMinus :
    Kboost * σMinus - σMinus * Kboost = -σMinus := by
  simpa [Kboost, smul_sub, smul_smul] using
    congrArg (fun X : M2C => (1 / 2 : ℂ) • X) comm_σ3_σMinus

/-- The compact Cartan generator has weight `+i` on the plus parabolic sheet. -/
theorem Kcirc_comm_sigmaPlus :
    Kcirc * σPlus - σPlus * Kcirc = Complex.I • σPlus := by
  simpa [Kcirc, smul_sub, smul_smul] using
    congrArg (fun X : M2C => (Complex.I / 2 : ℂ) • X) comm_σ3_σPlus

/-- The compact Cartan generator has weight `-i` on the minus parabolic sheet. -/
theorem Kcirc_comm_sigmaMinus :
    Kcirc * σMinus - σMinus * Kcirc = (-Complex.I) • σMinus := by
  simpa [Kcirc, smul_sub, smul_smul] using
    congrArg (fun X : M2C => (Complex.I / 2 : ℂ) • X) comm_σ3_σMinus

/-- The two parabolic sheets therefore carry opposite real and compact Cartan
weights under one commuting operator connection. -/
theorem two_sheet_cartan_weight_packet :
    (Kboost * σPlus - σPlus * Kboost = σPlus) ∧
    (Kboost * σMinus - σMinus * Kboost = -σMinus) ∧
    (Kcirc * σPlus - σPlus * Kcirc = Complex.I • σPlus) ∧
    (Kcirc * σMinus - σMinus * Kcirc = (-Complex.I) • σMinus) ∧
    wedge (operatorConnection Kboost Kcirc) (operatorConnection Kboost Kcirc)
        etaTangent thetaTangent = 0 := by
  exact ⟨Kboost_comm_sigmaPlus,
    Kboost_comm_sigmaMinus,
    Kcirc_comm_sigmaPlus,
    Kcirc_comm_sigmaMinus,
    canonical_connection_wedge_eta_theta_zero⟩

end InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge

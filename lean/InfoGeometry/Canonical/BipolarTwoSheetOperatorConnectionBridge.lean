import InfoGeometry.Canonical.BipolarTwoSheetParabolicCausalBoundaryBridge
import InfoGeometry.Canonical.BipolarLogSL2
import InfoGeometry.Analysis.BipolarPlanarHodgePair
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra
import InfoGeometry.Information.ModularSurprisalDerivationBridge
import InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms
import Mathlib.Tactic

/-!
# Two-sheet bipolar operator connection

This file formalizes the finite operator-connection layer suggested by the
bipolar/two-sheet construction. It deliberately separates four levels:

* the tangent carrier is the real two-coordinate plane `(dη,dθ)`;
* an operator-valued one-form assigns fixed algebra generators to those two directions;
* its algebraic self-wedge is exactly the commutator curvature term;
* the combined logarithmic Cartan generator has the two parabolic sheets as
  opposite adjoint eigenoperators, and the already-owned diagonal half-lift
  integrates those infinitesimal weights by finite conjugation.

For the canonical Pauli Cartan realization

`Kboost = σ3/2`, `Kcirc = i σ3/2`,

the two generators commute. Hence the commutator contribution to curvature
vanishes, while their adjoint actions on the two parabolic sheet generators
`σPlus, σMinus` carry opposite weights.

The finite group-level statement uses the repository-owned
`BipolarLogSL2.halfLogLift`; no parallel matrix-exponential series is introduced.
No nonconstant Maurer--Cartan theorem, gauge bundle, BKM metric identification,
or metriplectic dynamics is inferred here.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarPlanarHodgePair
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Physics.ChiralCausalCone
open InfoGeometry.Canonical.BipolarLogSL2

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

/-- Combined logarithmic Cartan generator
`K(s) = η(s) Kboost + θ(s) Kcirc`. -/
def logarithmicCartanGenerator (s : ℂ) : M2C :=
  (eta s : ℂ) • Kboost + (theta s : ℂ) • Kcirc

/-- The scalar eigenvalue on the plus sheet is exactly `η + i θ`. -/
def plusCartanWeight (s : ℂ) : ℂ :=
  (eta s : ℂ) + (theta s : ℂ) * Complex.I

/-- The minus-sheet eigenvalue is the negative plus-sheet weight. -/
def minusCartanWeight (s : ℂ) : ℂ :=
  -plusCartanWeight s

/-- The combined logarithmic generator acts on `σPlus` with eigenvalue
`η + i θ`. -/
theorem logarithmicCartan_comm_sigmaPlus (s : ℂ) :
    logarithmicCartanGenerator s * σPlus -
        σPlus * logarithmicCartanGenerator s =
      plusCartanWeight s • σPlus := by
  rw [logarithmicCartanGenerator]
  simp only [add_mul, mul_add, smul_mul, mul_smul, sub_eq_add_neg]
  rw [show
      (eta s : ℂ) • (Kboost * σPlus) +
          (theta s : ℂ) • (Kcirc * σPlus) +
          -(σPlus * ((eta s : ℂ) • Kboost) +
            σPlus * ((theta s : ℂ) • Kcirc)) =
        (eta s : ℂ) • (Kboost * σPlus - σPlus * Kboost) +
          (theta s : ℂ) • (Kcirc * σPlus - σPlus * Kcirc) by
      module]
  rw [Kboost_comm_sigmaPlus, Kcirc_comm_sigmaPlus]
  simp [plusCartanWeight, smul_smul]
  ring

/-- The combined logarithmic generator acts on `σMinus` with the opposite
adjoint eigenvalue. -/
theorem logarithmicCartan_comm_sigmaMinus (s : ℂ) :
    logarithmicCartanGenerator s * σMinus -
        σMinus * logarithmicCartanGenerator s =
      minusCartanWeight s • σMinus := by
  rw [logarithmicCartanGenerator]
  simp only [add_mul, mul_add, smul_mul, mul_smul, sub_eq_add_neg]
  rw [show
      (eta s : ℂ) • (Kboost * σMinus) +
          (theta s : ℂ) • (Kcirc * σMinus) +
          -(σMinus * ((eta s : ℂ) • Kboost) +
            σMinus * ((theta s : ℂ) • Kcirc)) =
        (eta s : ℂ) • (Kboost * σMinus - σMinus * Kboost) +
          (theta s : ℂ) • (Kcirc * σMinus - σMinus * Kcirc) by
      module]
  rw [Kboost_comm_sigmaMinus, Kcirc_comm_sigmaMinus]
  simp [minusCartanWeight, plusCartanWeight, smul_smul]
  ring

/-- The complex Cartan weight is exactly the principal logarithmic coordinate. -/
theorem plusCartanWeight_eq_bipolarLog (s : ℂ) :
    plusCartanWeight s = bipolarLog s := by
  apply Complex.ext <;> simp [plusCartanWeight, eta, theta]

/-- Explicit inverse of the repository-owned principal-log half-lift. -/
def halfLogLiftInv (s : ℂ) : M2C :=
  !![minusWeight s, 0;
     0, plusWeight s]

/-- The explicit inverse multiplies with the half-lift to the identity. -/
theorem halfLogLift_mul_inv (s : ℂ) :
    halfLogLift s * halfLogLiftInv s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfLogLift, halfLogLiftInv, Matrix.mul_apply, Fin.sum_univ_two,
      plusWeight_mul_minusWeight]

/-- Finite adjoint flow generated by the logarithmic Cartan lift. This is the
matrix-group realization of `exp(ad_K)` and avoids introducing a parallel
infinite-series matrix exponential. -/
def finiteAdjointFlow (s : ℂ) (X : M2C) : M2C :=
  halfLogLift s * X * halfLogLiftInv s

/-- The integrated adjoint flow has weight `exp(W)` on the plus parabolic sheet. -/
theorem finiteAdjointFlow_sigmaPlus (s : ℂ) :
    finiteAdjointFlow s σPlus = Complex.exp (bipolarLog s) • σPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteAdjointFlow, halfLogLift, halfLogLiftInv, plusWeight, minusWeight,
      σPlus, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add,
      Matrix.smul_apply] <;>
    ring_nf

/-- The integrated adjoint flow has the opposite weight `exp(-W)` on the minus
parabolic sheet. -/
theorem finiteAdjointFlow_sigmaMinus (s : ℂ) :
    finiteAdjointFlow s σMinus = Complex.exp (-bipolarLog s) • σMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteAdjointFlow, halfLogLift, halfLogLiftInv, plusWeight, minusWeight,
      σMinus, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add,
      Matrix.smul_apply] <;>
    ring_nf

/-- On the punctured bipolar domain, the plus-sheet finite adjoint weight is
exactly the Cayley coordinate `q(s)`. -/
theorem finiteAdjointFlow_sigmaPlus_eq_crossRatio
    {s : ℂ} (hs : s ∈ punctured01) :
    finiteAdjointFlow s σPlus = crossRatio01 s • σPlus := by
  rw [finiteAdjointFlow_sigmaPlus, exp_bipolarLog hs]

/-- On the punctured bipolar domain, the minus-sheet finite adjoint weight is
exactly `q(s)⁻¹`. -/
theorem finiteAdjointFlow_sigmaMinus_eq_crossRatio_inv
    {s : ℂ} (hs : s ∈ punctured01) :
    finiteAdjointFlow s σMinus = (crossRatio01 s)⁻¹ • σMinus := by
  rw [finiteAdjointFlow_sigmaMinus, Complex.exp_neg, exp_bipolarLog hs]

/-- Closed scalar-to-operator bridge: the infinitesimal adjoint eigenvalue is
`±W`, and the finite adjoint action carries the multiplicative weights
`q^{±1}`. -/
theorem logarithmic_cartan_adjoint_flow_packet
    {s : ℂ} (hs : s ∈ punctured01) :
    (logarithmicCartanGenerator s * σPlus - σPlus * logarithmicCartanGenerator s =
      bipolarLog s • σPlus) ∧
    (logarithmicCartanGenerator s * σMinus - σMinus * logarithmicCartanGenerator s =
      (-bipolarLog s) • σMinus) ∧
    finiteAdjointFlow s σPlus = crossRatio01 s • σPlus ∧
    finiteAdjointFlow s σMinus = (crossRatio01 s)⁻¹ • σMinus := by
  constructor
  · rw [logarithmicCartan_comm_sigmaPlus, plusCartanWeight_eq_bipolarLog]
  constructor
  · rw [logarithmicCartan_comm_sigmaMinus]
    simp [minusCartanWeight, plusCartanWeight_eq_bipolarLog]
  exact ⟨finiteAdjointFlow_sigmaPlus_eq_crossRatio hs,
    finiteAdjointFlow_sigmaMinus_eq_crossRatio_inv hs⟩

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

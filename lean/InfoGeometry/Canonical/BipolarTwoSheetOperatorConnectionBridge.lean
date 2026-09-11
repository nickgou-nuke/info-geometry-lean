import InfoGeometry.Canonical.BipolarTwoSheetParabolicCausalBoundaryBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BipolarLogSL2
import InfoGeometry.Analysis.BipolarPlanarHodgePair
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge

open InfoGeometry.Analysis.BipolarPlanarHodgePair
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Physics.ChiralCausalCone
open InfoGeometry.Canonical.BipolarLogSL2

abbrev Tangent2 := PlaneCovector
abbrev M2C := InfoGeometry.Physics.ChiralCausalCone.M2C

def etaTangent : Tangent2 := ![1, 0]
def thetaTangent : Tangent2 := ![0, 1]

def operatorConnection (Kη Kθ : M2C) : Op1Form ℝ Tangent2 M2C where
  toFun v := v 0 • Kη + v 1 • Kθ
  map_add' u v := by
    ext i j
    simp [Matrix.add_apply, add_smul]
    ring
  map_smul' c v := by
    ext i j
    simp [Matrix.add_apply, mul_smul]

@[simp] theorem operatorConnection_eta (Kη Kθ : M2C) :
    operatorConnection Kη Kθ etaTangent = Kη := by
  ext i j
  simp [operatorConnection, etaTangent]

@[simp] theorem operatorConnection_theta (Kη Kθ : M2C) :
    operatorConnection Kη Kθ thetaTangent = Kθ := by
  ext i j
  simp [operatorConnection, thetaTangent]

theorem wedge_connection_eta_theta (Kη Kθ : M2C) :
    wedge (operatorConnection Kη Kθ) (operatorConnection Kη Kθ)
        etaTangent thetaTangent = Kη * Kθ - Kθ * Kη := by
  rw [wedge_apply, operatorConnection_eta, operatorConnection_theta]

theorem wedge_connection_eta_theta_zero_of_commute
    (Kη Kθ : M2C) (h_comm : Kη * Kθ = Kθ * Kη) :
    wedge (operatorConnection Kη Kθ) (operatorConnection Kη Kθ)
        etaTangent thetaTangent = 0 := by
  rw [wedge_connection_eta_theta, h_comm, sub_self]

theorem wedge_connection_apply (Kη Kθ : M2C) (v w : Tangent2) :
    wedge (operatorConnection Kη Kθ) (operatorConnection Kη Kθ) v w =
      (v 0 * w 1 - v 1 * w 0) • (Kη * Kθ - Kθ * Kη) := by
  simp [wedge_apply, operatorConnection, mul_add, add_mul,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]
  module

def Kboost : M2C := (1 / 2 : ℂ) • σ3c
def Kcirc : M2C := (Complex.I / 2 : ℂ) • σ3c

theorem Kboost_Kcirc_commute : Kboost * Kcirc - Kcirc * Kboost = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Kboost, Kcirc, σ3c] <;> ring

theorem canonical_connection_wedge_eta_theta_zero :
    wedge (operatorConnection Kboost Kcirc) (operatorConnection Kboost Kcirc)
        etaTangent thetaTangent = 0 := by
  exact wedge_connection_eta_theta_zero_of_commute Kboost Kcirc
    (sub_eq_zero.mp Kboost_Kcirc_commute)

theorem Kboost_comm_sigmaPlus :
    Kboost * σPlus - σPlus * Kboost = σPlus := by
  simpa [Kboost, smul_sub, smul_smul] using
    congrArg (fun X : M2C => (1 / 2 : ℂ) • X) comm_σ3_σPlus

theorem Kboost_comm_sigmaMinus :
    Kboost * σMinus - σMinus * Kboost = -σMinus := by
  simpa [Kboost, smul_sub, smul_smul] using
    congrArg (fun X : M2C => (1 / 2 : ℂ) • X) comm_σ3_σMinus

theorem Kcirc_comm_sigmaPlus :
    Kcirc * σPlus - σPlus * Kcirc = Complex.I • σPlus := by
  simpa [Kcirc, smul_sub, smul_smul] using
    congrArg (fun X : M2C => (Complex.I / 2 : ℂ) • X) comm_σ3_σPlus

theorem Kcirc_comm_sigmaMinus :
    Kcirc * σMinus - σMinus * Kcirc = (-Complex.I) • σMinus := by
  simpa [Kcirc, smul_sub, smul_smul] using
    congrArg (fun X : M2C => (Complex.I / 2 : ℂ) • X) comm_σ3_σMinus

/-! The logarithmic Cartan element.  The real parameters are coerced into the
complex coefficient field of the matrix algebra. -/

def logarithmicCartan (η θ : ℝ) : M2C :=
  (η : ℂ) • Kboost + (θ : ℂ) • Kcirc

def bipolarLogarithmicCartan (s : ℂ) : M2C :=
  logarithmicCartan (eta s) (theta s)

theorem logarithmicCartan_comm_sigmaPlus (η θ : ℝ) :
    logarithmicCartan η θ * σPlus - σPlus * logarithmicCartan η θ =
      ((η : ℂ) + Complex.I * (θ : ℂ)) • σPlus := by
  calc
    logarithmicCartan η θ * σPlus - σPlus * logarithmicCartan η θ =
        (η : ℂ) • (Kboost * σPlus - σPlus * Kboost) +
          (θ : ℂ) • (Kcirc * σPlus - σPlus * Kcirc) := by
            simp [logarithmicCartan, add_mul, mul_add]
            module
    _ = ((η : ℂ) + Complex.I * (θ : ℂ)) • σPlus := by
      rw [Kboost_comm_sigmaPlus, Kcirc_comm_sigmaPlus]
      module

theorem logarithmicCartan_comm_sigmaMinus (η θ : ℝ) :
    logarithmicCartan η θ * σMinus - σMinus * logarithmicCartan η θ =
      (-((η : ℂ) + Complex.I * (θ : ℂ))) • σMinus := by
  calc
    logarithmicCartan η θ * σMinus - σMinus * logarithmicCartan η θ =
        (η : ℂ) • (Kboost * σMinus - σMinus * Kboost) +
          (θ : ℂ) • (Kcirc * σMinus - σMinus * Kcirc) := by
            simp [logarithmicCartan, add_mul, mul_add]
            module
    _ = (-((η : ℂ) + Complex.I * (θ : ℂ))) • σMinus := by
      rw [Kboost_comm_sigmaMinus, Kcirc_comm_sigmaMinus]
      module

theorem bipolarLogarithmicCartan_comm_sigmaPlus (s : ℂ) :
    bipolarLogarithmicCartan s * σPlus - σPlus * bipolarLogarithmicCartan s =
      ((eta s : ℂ) + Complex.I * (theta s : ℂ)) • σPlus := by
  exact logarithmicCartan_comm_sigmaPlus (eta s) (theta s)

theorem bipolarLogarithmicCartan_comm_sigmaMinus (s : ℂ) :
    bipolarLogarithmicCartan s * σMinus - σMinus * bipolarLogarithmicCartan s =
      (-((eta s : ℂ) + Complex.I * (theta s : ℂ))) • σMinus := by
  exact logarithmicCartan_comm_sigmaMinus (eta s) (theta s)

theorem bipolar_operator_weight_packet {s : ℂ} (hs : s ∈ punctured01) :
    (Complex.exp ((eta s : ℂ) + Complex.I * (theta s : ℂ)) = crossRatio01 s) ∧
    (bipolarLogarithmicCartan s * σPlus - σPlus * bipolarLogarithmicCartan s =
      ((eta s : ℂ) + Complex.I * (theta s : ℂ)) • σPlus) ∧
    (bipolarLogarithmicCartan s * σMinus - σMinus * bipolarLogarithmicCartan s =
      (-((eta s : ℂ) + Complex.I * (theta s : ℂ))) • σMinus) := by
  refine ⟨?_, bipolarLogarithmicCartan_comm_sigmaPlus s,
    bipolarLogarithmicCartan_comm_sigmaMinus s⟩
  simpa [mul_comm] using (exp_eta_theta hs)

theorem bipolarLogarithmicCartan_criticalLine (y : ℝ) :
    bipolarLogarithmicCartan (criticalLine y) =
      (theta (criticalLine y) : ℂ) • Kcirc := by
  simp [bipolarLogarithmicCartan, logarithmicCartan, eta_criticalLine]

theorem bipolarLogarithmicCartan_criticalLine_comm_sigmaPlus (y : ℝ) :
    bipolarLogarithmicCartan (criticalLine y) * σPlus -
        σPlus * bipolarLogarithmicCartan (criticalLine y) =
      (Complex.I * (theta (criticalLine y) : ℂ)) • σPlus := by
  rw [bipolarLogarithmicCartan_comm_sigmaPlus, eta_criticalLine]
  simp [zero_add]

theorem bipolarLogarithmicCartan_criticalLine_comm_sigmaMinus (y : ℝ) :
    bipolarLogarithmicCartan (criticalLine y) * σMinus -
        σMinus * bipolarLogarithmicCartan (criticalLine y) =
      (-Complex.I * (theta (criticalLine y) : ℂ)) • σMinus := by
  rw [bipolarLogarithmicCartan_comm_sigmaMinus, eta_criticalLine]
  simp [zero_add]

/-! ### Finite adjoint readout

The diagonal torus lift is used directly here.  Its inverse is the diagonal
matrix with the two entries exchanged; this keeps the finite statement in the
native matrix carrier and does not introduce a second exponential or a
branch-dependent matrix logarithm.
-/

def halfLogLiftInv (s : ℂ) : M2C :=
  !![minusWeight s, 0; 0, plusWeight s]

def torusAdjoint (s : ℂ) (X : M2C) : M2C :=
  halfLogLift s * X *
    !![minusWeight s, 0;
       0, plusWeight s]

theorem halfLogLift_mul_explicitInverse (s : ℂ) :
    halfLogLift s *
        !![minusWeight s, 0;
           0, plusWeight s] = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [halfLogLift, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals simpa only [mul_comm] using (plusWeight_mul_minusWeight s)

theorem explicitInverse_mul_halfLogLift (s : ℂ) :
    (!![minusWeight s, 0;
        0, plusWeight s] : M2C) * halfLogLift s = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [halfLogLift, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals simpa only [mul_comm] using (plusWeight_mul_minusWeight s)

theorem torusAdjoint_sigmaPlus {s : ℂ} (hs : s ∈ punctured01) :
    torusAdjoint s σPlus = crossRatio01 s • σPlus := by
  unfold torusAdjoint
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfLogLift, plusWeight, minusWeight, σPlus, Matrix.mul_apply,
      Fin.sum_univ_two, ← Complex.exp_add,
      ← exp_bipolarLog hs]

theorem torusAdjoint_sigmaMinus {s : ℂ} (hs : s ∈ punctured01) :
    torusAdjoint s σMinus = (crossRatio01 s)⁻¹ • σMinus := by
  unfold torusAdjoint
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [halfLogLift, plusWeight, minusWeight, σMinus, Matrix.mul_apply,
      Fin.sum_univ_two, ← Complex.exp_add,
      ← exp_bipolarLog hs, Complex.exp_neg]

/-! A canonical name for the finite adjoint action used by downstream
period and descent owners.  It is definitionally the existing torus action;
the alias keeps the carrier unique while exposing the structural name. -/
def finiteAdjointFlow (s : ℂ) (X : M2C) : M2C :=
  torusAdjoint s X

theorem finiteAdjointFlow_sigmaPlus_eq_crossRatio
    {s : ℂ} (hs : s ∈ punctured01) :
    finiteAdjointFlow s σPlus = crossRatio01 s • σPlus := by
  exact torusAdjoint_sigmaPlus hs

theorem finiteAdjointFlow_sigmaMinus_eq_crossRatio_inv
    {s : ℂ} (hs : s ∈ punctured01) :
    finiteAdjointFlow s σMinus = (crossRatio01 s)⁻¹ • σMinus := by
  exact torusAdjoint_sigmaMinus hs



theorem two_sheet_cartan_weight_packet :
    (Kboost * σPlus - σPlus * Kboost = σPlus) ∧
    (Kboost * σMinus - σMinus * Kboost = -σMinus) ∧
    (Kcirc * σPlus - σPlus * Kcirc = Complex.I • σPlus) ∧
    (Kcirc * σMinus - σMinus * Kcirc = (-Complex.I) • σMinus) ∧
    wedge (operatorConnection Kboost Kcirc) (operatorConnection Kboost Kcirc)
        etaTangent thetaTangent = 0 := by
  exact ⟨Kboost_comm_sigmaPlus, Kboost_comm_sigmaMinus,
    Kcirc_comm_sigmaPlus, Kcirc_comm_sigmaMinus,
    canonical_connection_wedge_eta_theta_zero⟩

end InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge

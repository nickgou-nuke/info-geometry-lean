import InfoGeometry.Clifford.DiracPauliGamma
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Section 5: Clifford Structure (Pauli-Dirac)

γ⁰ = diag(I, -I), γ^i = [[0,σ_i],[-σ_i,0]]
Clifford: {γ^a, γ^b} = 2·η^{ab}·I₄  ((+---) signature)
-/

noncomputable section

namespace Section5

abbrev DiracSpinor : Type :=
  InfoGeometry.Clifford.DiracPauliGamma.DiracSpinor

abbrev DiracMatrix : Type :=
  InfoGeometry.Clifford.DiracPauliGamma.DiracMatrix

abbrev γ0 : DiracMatrix :=
  InfoGeometry.Clifford.DiracPauliGamma.gamma0

abbrev γ1 : DiracMatrix :=
  InfoGeometry.Clifford.DiracPauliGamma.gamma1

abbrev γ2 : DiracMatrix :=
  InfoGeometry.Clifford.DiracPauliGamma.gamma2

abbrev γ3 : DiracMatrix :=
  InfoGeometry.Clifford.DiracPauliGamma.gamma3

abbrev γ5 : DiracMatrix :=
  InfoGeometry.Clifford.DiracPauliGamma.gamma5

abbrev γ : Fin 4 → DiracMatrix :=
  InfoGeometry.Clifford.DiracPauliGamma.gamma

abbrev η : Fin 4 → Fin 4 → ℂ :=
  InfoGeometry.Clifford.DiracPauliGamma.eta

theorem γ0_sq : γ0 * γ0 = (1 : DiracMatrix) :=
  InfoGeometry.Clifford.DiracPauliGamma.gamma0_mul_self

theorem γi_sq_neg : γ1 * γ1 = -(1 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ2 * γ2 = -(1 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ3 * γ3 = -(1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨InfoGeometry.Clifford.DiracPauliGamma.gamma1_mul_self,
    InfoGeometry.Clifford.DiracPauliGamma.gamma2_mul_self,
    InfoGeometry.Clifford.DiracPauliGamma.gamma3_mul_self⟩

theorem clifford_anticomm : γ0 * γ1 + γ1 * γ0 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ0 * γ2 + γ2 * γ0 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ0 * γ3 + γ3 * γ0 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ1 * γ2 + γ2 * γ1 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ1 * γ3 + γ3 * γ1 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ2 * γ3 + γ3 * γ2 = (0 : Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨InfoGeometry.Clifford.DiracPauliGamma.gamma0_gamma1_anticomm,
    InfoGeometry.Clifford.DiracPauliGamma.gamma0_gamma2_anticomm,
    InfoGeometry.Clifford.DiracPauliGamma.gamma0_gamma3_anticomm,
    InfoGeometry.Clifford.DiracPauliGamma.gamma1_gamma2_anticomm,
    InfoGeometry.Clifford.DiracPauliGamma.gamma1_gamma3_anticomm,
    InfoGeometry.Clifford.DiracPauliGamma.gamma2_gamma3_anticomm⟩

theorem γ5_anticomm : γ5 * γ0 + γ0 * γ5 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ5 * γ1 + γ1 * γ5 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ5 * γ2 + γ2 * γ5 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ5 * γ3 + γ3 * γ5 = (0 : Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨InfoGeometry.Clifford.DiracPauliGamma.gamma5_anticomm 0,
    InfoGeometry.Clifford.DiracPauliGamma.gamma5_anticomm 1,
    InfoGeometry.Clifford.DiracPauliGamma.gamma5_anticomm 2,
    InfoGeometry.Clifford.DiracPauliGamma.gamma5_anticomm 3⟩

theorem gamma5_product : Complex.I • (((γ0 * γ1) * γ2) * γ3) = γ5 :=
  InfoGeometry.Clifford.DiracPauliGamma.gamma5_eq_i_mul_product

theorem clifford_anticomm_full (mu nu : Fin 4) :
    γ mu * γ nu + γ nu * γ mu = (2 * η mu nu) • (1 : DiracMatrix) :=
  InfoGeometry.Clifford.DiracPauliGamma.gamma_anticomm mu nu

abbrev lorentzGenerator : Fin 4 → Fin 4 → DiracMatrix :=
  InfoGeometry.Clifford.DiracPauliGamma.lorentzGenerator

theorem commutator_eq_neg_four_i_lorentzGenerator (mu nu : Fin 4) :
    γ mu * γ nu - γ nu * γ mu = (-4 * Complex.I) • lorentzGenerator mu nu :=
  InfoGeometry.Clifford.DiracPauliGamma.commutator_eq_neg_four_i_lorentzGenerator mu nu

abbrev scalarBilinear : DiracSpinor → ℂ :=
  InfoGeometry.Clifford.DiracPauliGamma.scalarBilinear

abbrev vectorBilinear : Fin 4 → DiracSpinor → ℂ :=
  InfoGeometry.Clifford.DiracPauliGamma.vectorBilinear

abbrev bivectorBilinear : Fin 4 → Fin 4 → DiracSpinor → ℂ :=
  InfoGeometry.Clifford.DiracPauliGamma.bivectorBilinear

abbrev pseudoscalarBilinear : DiracSpinor → ℂ :=
  InfoGeometry.Clifford.DiracPauliGamma.pseudoscalarBilinear

abbrev axialBilinear : Fin 4 → DiracSpinor → ℂ :=
  InfoGeometry.Clifford.DiracPauliGamma.axialBilinear

end Section5

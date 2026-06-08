import InfoGeometry.Clifford.DiracPauliGamma

/-!
# Section 5: Clifford Structure (Pauli-Dirac)

γ⁰ = diag(I, -I), γ^i = [[0,σ_i],[-σ_i,0]]
Clifford: {γ^a, γ^b} = 2·η^{ab}·I₄  ((+---) signature)
-/

noncomputable section

namespace Section5

namespace G := InfoGeometry.Clifford.DiracPauliGamma

abbrev DiracSpinor : Type :=
  G.DiracSpinor

abbrev DiracMatrix : Type :=
  G.DiracMatrix

abbrev γ0 : DiracMatrix :=
  G.gamma0

abbrev γ1 : DiracMatrix :=
  G.gamma1

abbrev γ2 : DiracMatrix :=
  G.gamma2

abbrev γ3 : DiracMatrix :=
  G.gamma3

abbrev γ5 : DiracMatrix :=
  G.gamma5

abbrev γ : Fin 4 → DiracMatrix :=
  G.gamma

abbrev η : Fin 4 → Fin 4 → ℂ :=
  G.eta

theorem γ0_sq : γ0 * γ0 = (1 : DiracMatrix) :=
  G.gamma0_mul_self

theorem γi_sq_neg : γ1 * γ1 = -(1 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ2 * γ2 = -(1 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ3 * γ3 = -(1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨G.gamma1_mul_self, G.gamma2_mul_self, G.gamma3_mul_self⟩

theorem clifford_anticomm : γ0 * γ1 + γ1 * γ0 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ0 * γ2 + γ2 * γ0 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ0 * γ3 + γ3 * γ0 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ1 * γ2 + γ2 * γ1 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ1 * γ3 + γ3 * γ1 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ2 * γ3 + γ3 * γ2 = (0 : Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨G.gamma0_gamma1_anticomm, G.gamma0_gamma2_anticomm, G.gamma0_gamma3_anticomm,
    G.gamma1_gamma2_anticomm, G.gamma1_gamma3_anticomm, G.gamma2_gamma3_anticomm⟩

theorem γ5_anticomm : γ5 * γ0 + γ0 * γ5 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ5 * γ1 + γ1 * γ5 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ5 * γ2 + γ2 * γ5 = (0 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    γ5 * γ3 + γ3 * γ5 = (0 : Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨G.gamma5_anticomm 0, G.gamma5_anticomm 1, G.gamma5_anticomm 2,
    G.gamma5_anticomm 3⟩

theorem gamma5_product : Complex.I • (((γ0 * γ1) * γ2) * γ3) = γ5 :=
  G.gamma5_eq_i_mul_product

theorem clifford_anticomm_full (mu nu : Fin 4) :
    γ mu * γ nu + γ nu * γ mu = (2 * η mu nu) • (1 : DiracMatrix) :=
  G.gamma_anticomm mu nu

abbrev lorentzGenerator : Fin 4 → Fin 4 → DiracMatrix :=
  G.lorentzGenerator

theorem commutator_eq_neg_four_i_lorentzGenerator (mu nu : Fin 4) :
    γ mu * γ nu - γ nu * γ mu = (-4 * Complex.I) • lorentzGenerator mu nu :=
  G.commutator_eq_neg_four_i_lorentzGenerator mu nu

abbrev scalarBilinear : DiracSpinor → ℂ :=
  G.scalarBilinear

abbrev vectorBilinear : Fin 4 → DiracSpinor → ℂ :=
  G.vectorBilinear

abbrev bivectorBilinear : Fin 4 → Fin 4 → DiracSpinor → ℂ :=
  G.bivectorBilinear

abbrev pseudoscalarBilinear : DiracSpinor → ℂ :=
  G.pseudoscalarBilinear

abbrev axialBilinear : Fin 4 → DiracSpinor → ℂ :=
  G.axialBilinear

end Section5

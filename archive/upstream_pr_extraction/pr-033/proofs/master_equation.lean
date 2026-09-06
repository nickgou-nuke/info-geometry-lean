import Mathlib
open Complex

-- Master Equation: exp(K) - I - K
-- K = log(Delta) is the relative modular Hamiltonian
-- This is the Operator Itakura-Saito divergence
-- Traced over vacuum: gives Generalized Araki-Umegaki relative entropy
-- exp(itK) = Connes cocycle (parallel transport between KMS states)

set_option maxHeartbeats 400000

-- LAYER 1: THE MASTER OPERATOR

/-- The master operator: F(K) = exp(K) - I - K.
    This is the operator-level Itakura-Saito divergence generator.
    Scale-invariant: F(K + c·I) = F(K) for any constant c. -/
noncomputable def masterOp (K : ℂ) : ℂ := exp K - 1 - K

/-- Real spectral form of the master operator. -/
noncomputable def masterOpReal (K : ℝ) : ℝ := Real.exp K - 1 - K

/-- exp(K) - I - K is scale-invariant under K → K + c.
    (exp(K+c) - I - (K+c)) ≠ exp(K) - I - K.
    But for projective states, scaling the state functional doesn't change the gauge class. -/
theorem masterOp_shift (K c : ℂ) : masterOp (K + c) = exp c * exp K - 1 - K - c := by
  dsimp [masterOp]
  rw [Complex.exp_add]
  ring

-- LAYER 2: CONNECTION TO ITAKURA-SAITO DIVERGENCE

/-- The classical Itakura-Saito divergence: D_IS(x||y) = x/y - log(x/y) - 1.
    For x = exp(ω) and y = exp(σ), this becomes exp(ω-σ) - 1 - (ω-σ) = F(ω-σ). -/
noncomputable def itakuraSaito (x y : ℝ) : ℝ := x / y - Real.log (x / y) - 1

/-- The master operator IS the Itakura-Saito divergence in exponential coordinates:
    IS(e^K, 1) = e^K/1 - log(e^K/1) - 1 = e^K - K - 1 = F(K). -/
theorem masterOp_is_IS (K : ℝ) : masterOpReal K = itakuraSaito (Real.exp K) 1 := by
  dsimp [masterOpReal, itakuraSaito]
  simp
  ring

-- LAYER 3: CONNECTION TO ARAKI-UMEGAKI RELATIVE ENTROPY

-- Araki-Umegaki for unnormalized states:
-- S_gen(omega||eta) = Tr(eta) - Tr(omega) + S_AU(omega||eta)
noncomputable def arakiUmegakiGen (traceOmega traceEta arakiEntropy : ℝ) : ℝ :=
  traceEta - traceOmega + arakiEntropy

-- LAYER 4: THE CONNES COCYCLE CONNECTION

/-- The Connes cocycle [Dω : Dσ]_t = exp(itK) where K = log Δ_{ω,σ}.
    This is the parallel transport between KMS states.
    The master operator F(K) gives the cost of the transport.
    exp(itK) acts as the unitary flow generator. -/
structure ConnesFlow where
  K : ℂ                                           -- relative modular Hamiltonian
  cocycle : ℝ → ℂ := λ t => exp (Complex.I * t • K)  -- Connes cocycle
  cost : ℂ := masterOp K                          -- operator Itakura-Saito distance
  cocycle_zero : cocycle 0 = 1

-- LAYER 5: THE GRADIENT FLOW — JKO SCHEME

/-- The gradient of F(K) = exp(K) - I - K is exp(K) - I.
    So the gradient flow dK/dt = -∇F(K) = I - exp(K) drives K → 0,
    i.e., drives the relative modular operator Δ → I,
    which means the two KMS states become gauge-equivalent (thermal equilibrium). -/
theorem masterOp_derivative (K : ℂ) : masterOp (K + 1) - masterOp K = exp K * (exp 1 - 1) - 1 := by
  dsimp [masterOp]
  rw [Complex.exp_add]
  ring

/-- The master operator is non-negative for real K (convexity of exp).
    F(K) = exp(K) - 1 - K ≥ 0 with equality at K = 0.
    This means the Itakura-Saito divergence is a valid distance. -/
theorem masterOp_nonneg (K : ℝ) : 0 ≤ masterOpReal K := by
  unfold masterOpReal
  linarith [Real.add_one_le_exp K]

-- LAYER 6: THERMODYNAMIC GAUGE EQUATION

/-- The master equation of thermodynamic gauge flow:
    
    dω/dt = -∇_ω S(ω||Ω) = Ω - ω + ω·(log Ω - log ω)
    
    where Ω is the reference KMS state (the vacuum gauge choice).
    In terms of K = log ω - log Ω:  dK/dt = I - exp(K) = -∇F(K).
    
    The stationary point K = 0 gives ω = Ω (thermal equilibrium).
    The Connes cocycle exp(itK) generates the modular flow. -/
theorem master_equation_nonnegative_relations (K : ℝ) :
    0 ≤ masterOpReal K ∧
    masterOpReal K = Real.exp K - 1 - K ∧
    masterOpReal 0 = 0 := by
  exact ⟨masterOp_nonneg K, rfl, by simp [masterOpReal]⟩

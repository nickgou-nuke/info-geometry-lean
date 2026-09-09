import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import InfoGeometry.Canonical.Berezinian

/-!
# Supergraded Primon Algebra, Berezinian Dirichlet Convolution, Surprisal & Massieu Free Energy
-/

noncomputable section

namespace InfoGeometry.Topology.PrimonBerezinianMassieuBridge

open Complex

/-! ### 1. Supergraded Primon State Energy & Mobius Grading -/

/-- Total logarithmic energy of the primon state |n⟩ -/
def primonEnergy (n : ℝ) : ℝ :=
  Real.log n

/-- Discrete Gibbs probability p_n(beta) = n^{-beta} / Z -/
def gibbsProb (n beta Z : ℝ) : ℝ :=
  (n ^ (-beta)) / Z

/-- Surprisal (Self-Information) I_n = -ln(p_n) = beta * ln(n) + ln(Z) -/
def surprisal (n beta Z : ℝ) : ℝ :=
  beta * Real.log n + Real.log Z

/-- 🏆 THEOREM 1: Surprisal Decomposition into Energy and Massieu Potential -/
theorem surprisal_eq_energy_add_massieu (n beta Z : ℝ) (hn : 0 < n) (hZ : 0 < Z) :
    - Real.log (gibbsProb n beta Z) = surprisal n beta Z := by
  dsimp [gibbsProb, surprisal]
  have h_rpow_pos : 0 < n ^ (-beta) := Real.rpow_pos_of_pos hn (-beta)
  rw [Real.log_div (ne_of_gt h_rpow_pos) (ne_of_gt hZ)]
  rw [Real.log_rpow hn]
  ring

/-! ### 2. 2-Point Discrete Primon Model: Surprisal Expectation & Shannon Entropy -/

/-- Expectation of an observable X over a 2-point probability distribution (p1, p2) -/
def expectation2 (p1 p2 X1 X2 : ℝ) : ℝ :=
  p1 * X1 + p2 * X2

/-- Shannon entropy S = - (p1 * ln(p1) + p2 * ln(p2)) -/
def shannonEntropy2 (p1 p2 : ℝ) : ℝ :=
  - (p1 * Real.log p1 + p2 * Real.log p2)

/-- 🏆 THEOREM 2: Shannon Entropy Equals the Expectation of the Surprisal -/
theorem shannon_entropy_eq_expectation_surprisal (p1 p2 : ℝ) :
    shannonEntropy2 p1 p2 = expectation2 p1 p2 (- Real.log p1) (- Real.log p2) := by
  dsimp [shannonEntropy2, expectation2]
  ring

/-! ### 3. Massieu Characteristic Function & Free Energy Duality -/

/-- Massieu potential Phi(beta) = ln(Z) -/
def massieuPotential (Z : ℝ) : ℝ :=
  Real.log Z

/-- Helmholtz free energy F = - (1 / beta) * Phi(beta) = <E> - T * S -/
def helmholtzFreeEnergy (beta Z : ℝ) : ℝ :=
  - (1 / beta) * massieuPotential Z

/-- 🏆 THEOREM 3: Fundamental Legendre Relation <E> - T * S = F -/
theorem free_energy_legendre_relation
    (beta mean_E S Z : ℝ) (hbeta : beta ≠ 0)
    (h_entropy : S = beta * mean_E + massieuPotential Z) :
    mean_E - (1 / beta) * S = helmholtzFreeEnergy beta Z := by
  dsimp [helmholtzFreeEnergy]
  rw [h_entropy]
  have h1 : mean_E - (1 / beta) * (beta * mean_E + massieuPotential Z) =
      mean_E - (1 / beta) * (beta * mean_E) - (1 / beta) * massieuPotential Z := by ring
  rw [h1]
  have h_cancel : (1 / beta) * (beta * mean_E) = mean_E := by
    calc
      (1 / beta) * (beta * mean_E) = (1 / beta * beta) * mean_E := by ring
      _ = 1 * mean_E := by rw [one_div_mul_cancel hbeta]
      _ = mean_E := by ring
  rw [h_cancel]
  ring

/-! ### 4. Berezinian / Dirichlet Supertrace Boson-Fermion Cancellation -/

/-- 🏆 THEOREM 4: Algebraic Bosonic-Fermionic Dirichlet Cancellation ζ * (1/ζ) = 1 -/
theorem primon_boson_fermion_berezinian_cancellation (zeta_val : ℂ) (hzeta : zeta_val ≠ 0) :
    zeta_val * (1 / zeta_val) = 1 :=
  mul_one_div_cancel hzeta

/-! The product cancellation above is distinct from the Berezinian ratio. -/

/-- Reciprocal determinant blocks have Berezinian `a²`, not `1`. -/
theorem primon_reciprocal_blocks_berezinian (a : ℝ) (ha : a ≠ 0) :
    InfoGeometry.Canonical.Berezinian.ber a a⁻¹ (inv_ne_zero ha) = a ^ 2 :=
  by
    unfold InfoGeometry.Canonical.Berezinian.ber
    rw [div_inv_eq_mul]
    ring

/-! ### 5. Master Primon Berezinian Massieu Synthesis Packet -/

/-- 🏆 THEOREM 5: MASTER PRIMON BEREZINIAN MASSIEU SYNTHESIS PACKET -/
theorem primon_berezinian_massieu_master_packet
    (n beta Z : ℝ) (hn : 0 < n) (hZ : 0 < Z) (hbeta : beta ≠ 0)
    (p1 p2 mean_E S : ℝ)
    (h_entropy : S = beta * mean_E + massieuPotential Z)
    (zeta_val : ℂ) (hzeta : zeta_val ≠ 0) :
    -- 1. Surprisal decomposition
    (- Real.log (gibbsProb n beta Z) = surprisal n beta Z) ∧
    -- 2. Shannon entropy = expectation of surprisal
    (shannonEntropy2 p1 p2 = expectation2 p1 p2 (- Real.log p1) (- Real.log p2)) ∧
    -- 3. Free energy duality: <E> - T*S = F
    (mean_E - (1 / beta) * S = helmholtzFreeEnergy beta Z) ∧
    -- 4. Berezinian supertrace cancellation
    (zeta_val * (1 / zeta_val) = 1) := by
  refine ⟨surprisal_eq_energy_add_massieu n beta Z hn hZ,
          shannon_entropy_eq_expectation_surprisal p1 p2,
          free_energy_legendre_relation beta mean_E S Z hbeta h_entropy,
          primon_boson_fermion_berezinian_cancellation zeta_val hzeta⟩

end InfoGeometry.Topology.PrimonBerezinianMassieuBridge

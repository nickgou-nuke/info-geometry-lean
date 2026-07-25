import Mathlib.Tactic
open Real

namespace InfoGeometry.Fibonacci.FibAnyonThm1

noncomputable section

/-! Theorem 1: Fibonacci Fusion Rules -/

def φ : ℝ := (1 + Real.sqrt 5) / 2
def τ : ℝ := (1 - Real.sqrt 5) / 2

lemma h5sq : (Real.sqrt 5)^2 = (5 : ℝ) :=
  Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)

theorem golden_identity : φ^2 = φ + 1 := by
  dsimp [φ]
  calc
    ((1 + Real.sqrt 5) / 2)^2 = ((1 + Real.sqrt 5)^2) / 4 := by ring
    _ = (1 + 2*Real.sqrt 5 + (Real.sqrt 5)^2) / 4 := by ring
    _ = (1 + 2*Real.sqrt 5 + 5) / 4 := by rw [h5sq]
    _ = (6 + 2*Real.sqrt 5) / 4 := by ring
    _ = (3 + Real.sqrt 5) / 2 := by ring
    _ = (1 + Real.sqrt 5) / 2 + 1 := by ring

lemma φ_pos : φ > 0 := by
  dsimp [φ]
  have h5pos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  nlinarith

lemma φ_ne_zero : φ ≠ 0 := by linarith [φ_pos]

theorem tau_mul_phi_eq_neg_one : τ * φ = -1 := by
  dsimp [τ, φ]
  calc
    ((1 - Real.sqrt 5) / 2) * ((1 + Real.sqrt 5) / 2) = ((1 - Real.sqrt 5) * (1 + Real.sqrt 5)) / 4 := by ring
    _ = (1 - (Real.sqrt 5)^2) / 4 := by ring
    _ = (1 - 5) / 4 := by rw [h5sq]
    _ = (-4) / 4 := by ring
    _ = -1 := by ring

theorem tau_eq_neg_inv_phi : τ = -(1 / φ) := by
  calc
    τ = (τ * φ) / φ := by field_simp [φ_ne_zero]
    _ = (-1) / φ := by rw [tau_mul_phi_eq_neg_one]
    _ = -(1 / φ) := by ring

inductive FibSector : Type
  | one | tau
  deriving DecidableEq

open FibSector

def fuse : FibSector → FibSector → List FibSector
  | one, x => [x]
  | x, one => [x]
  | tau, tau => [one, tau]

def dim_one : ℝ := 1
def dim_tau : ℝ := φ

theorem fusion_dim_identity : dim_tau^2 = dim_tau + dim_one := by
  dsimp [dim_tau, dim_one, φ]
  exact golden_identity

end

end InfoGeometry.Fibonacci.FibAnyonThm1

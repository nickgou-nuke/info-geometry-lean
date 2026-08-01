import Mathlib

noncomputable section

namespace InfoGeometry.Algebra.PseudoEuclideanCliffordSignatureBridge

/-- **Definition**: Cl(1,1) Split Clifford Generators γ₀ and γ₁.
    γ₀² = +1, γ₁² = -1, γ₀ γ₁ + γ₁ γ₀ = 0. -/
@[ext]
structure Cl11Generators (R : Type*) [Ring R] where
  gamma0 : R
  gamma1 : R
  gamma0_sq : gamma0 * gamma0 = 1
  gamma1_sq : gamma1 * gamma1 = -1
  anticomm : gamma0 * gamma1 + gamma1 * gamma0 = 0

namespace Cl11Generators

variable {R : Type*} [Ring R] (g : Cl11Generators R)

/-- Pseudoscalar / Volume Form for Cl(1,1): Γ = γ₀ γ₁. -/
def volumeForm : R := g.gamma0 * g.gamma1

/-- **Theorem**: Square of Cl(1,1) Volume Form is +1.
    Γ² = (γ₀ γ₁) (γ₀ γ₁) = - γ₀ γ₁ γ₁ γ₀ = - γ₀ (-1) γ₀ = γ₀² = 1. -/
theorem volumeForm_squared : g.volumeForm * g.volumeForm = 1 := by
  dsimp [volumeForm]
  have h_anticomm : g.gamma1 * g.gamma0 = - (g.gamma0 * g.gamma1) :=
    eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact g.anticomm)
  calc g.gamma0 * g.gamma1 * (g.gamma0 * g.gamma1)
    _ = g.gamma0 * (g.gamma1 * g.gamma0) * g.gamma1 := by noncomm_ring
    _ = g.gamma0 * (- (g.gamma0 * g.gamma1)) * g.gamma1 := by rw [h_anticomm]
    _ = - (g.gamma0 * g.gamma0 * (g.gamma1 * g.gamma1)) := by noncomm_ring
    _ = - (1 * (-1)) := by rw [g.gamma0_sq, g.gamma1_sq]
    _ = 1 := by simp

end Cl11Generators

/-- **Definition**: Cl(1,3) Minkowski Spacetime Algebra Generators.
    γ₀² = +1, γ₁² = γ₂² = γ₃² = -1. -/
structure Cl13SpacetimeGenerators (R : Type*) [Ring R] where
  gamma0 : R
  gamma1 : R
  gamma2 : R
  gamma3 : R
  gamma0_sq : gamma0 * gamma0 = 1
  gamma1_sq : gamma1 * gamma1 = -1
  gamma2_sq : gamma2 * gamma2 = -1
  gamma3_sq : gamma3 * gamma3 = -1
  anticomm_01 : gamma0 * gamma1 + gamma1 * gamma0 = 0
  anticomm_02 : gamma0 * gamma2 + gamma2 * gamma0 = 0
  anticomm_03 : gamma0 * gamma3 + gamma3 * gamma0 = 0
  anticomm_12 : gamma1 * gamma2 + gamma2 * gamma1 = 0
  anticomm_13 : gamma1 * gamma3 + gamma3 * gamma1 = 0
  anticomm_23 : gamma2 * gamma3 + gamma3 * gamma2 = 0

namespace Cl13SpacetimeGenerators

variable {R : Type*} [Ring R] (g : Cl13SpacetimeGenerators R)

/-- Spacetime Volume Form / Chiral Pseudoscalar γ₅ = γ₀ γ₁ γ₂ γ₃. -/
def gamma5 : R := g.gamma0 * g.gamma1 * g.gamma2 * g.gamma3

/-- **Theorem**: Parity-Flipping / Chiral Anticommutation {γ₅, γ₀} = 0. -/
theorem gamma5_anticomm_gamma0 :
    g.gamma5 * g.gamma0 + g.gamma0 * g.gamma5 = 0 := by
  dsimp [gamma5]
  have h01 : g.gamma0 * g.gamma1 = - (g.gamma1 * g.gamma0) := eq_neg_of_add_eq_zero_left g.anticomm_01
  have h02 : g.gamma0 * g.gamma2 = - (g.gamma2 * g.gamma0) := eq_neg_of_add_eq_zero_left g.anticomm_02
  have h03 : g.gamma0 * g.gamma3 = - (g.gamma3 * g.gamma0) := eq_neg_of_add_eq_zero_left g.anticomm_03
  have h_left : g.gamma0 * g.gamma1 * g.gamma2 * g.gamma3 * g.gamma0 = - (g.gamma1 * g.gamma2 * g.gamma3) := by
    calc g.gamma0 * g.gamma1 * g.gamma2 * g.gamma3 * g.gamma0
      _ = - (g.gamma1 * g.gamma0) * g.gamma2 * g.gamma3 * g.gamma0 := by rw [h01]
      _ = - g.gamma1 * (g.gamma0 * g.gamma2) * g.gamma3 * g.gamma0 := by noncomm_ring
      _ = g.gamma1 * (g.gamma2 * g.gamma0) * g.gamma3 * g.gamma0 := by rw [h02]; noncomm_ring
      _ = g.gamma1 * g.gamma2 * (g.gamma0 * g.gamma3) * g.gamma0 := by noncomm_ring
      _ = - g.gamma1 * g.gamma2 * (g.gamma3 * g.gamma0) * g.gamma0 := by rw [h03]; noncomm_ring
      _ = - (g.gamma1 * g.gamma2 * g.gamma3 * (g.gamma0 * g.gamma0)) := by noncomm_ring
      _ = - (g.gamma1 * g.gamma2 * g.gamma3 * 1) := by rw [g.gamma0_sq]
      _ = - (g.gamma1 * g.gamma2 * g.gamma3) := by noncomm_ring
  have h_right : g.gamma0 * (g.gamma0 * g.gamma1 * g.gamma2 * g.gamma3) = g.gamma1 * g.gamma2 * g.gamma3 := by
    calc g.gamma0 * (g.gamma0 * g.gamma1 * g.gamma2 * g.gamma3)
      _ = (g.gamma0 * g.gamma0) * g.gamma1 * g.gamma2 * g.gamma3 := by noncomm_ring
      _ = 1 * g.gamma1 * g.gamma2 * g.gamma3 := by rw [g.gamma0_sq]
      _ = g.gamma1 * g.gamma2 * g.gamma3 := by noncomm_ring
  rw [h_left, h_right]
  noncomm_ring

end Cl13SpacetimeGenerators

end InfoGeometry.Algebra.PseudoEuclideanCliffordSignatureBridge

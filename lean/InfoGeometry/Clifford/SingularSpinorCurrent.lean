/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HestenesCliffordKreinFinite
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.Tactic.NoncommRing

/-! # An explicit nonzero even spinor with a nonzero null current

Work in the existing native real Clifford algebra of signature `(+---)`.
The even element `ψ = 1 + γ₁γ₀` has zero product with its native reversion,
while its actual sandwich `ψγ₀reverse(ψ)` is `2 • (γ₀ + γ₁)`, a nonzero vector
whose Clifford square vanishes. Nonvanishing follows from the injective vector
inclusion, transported through Mathlib's Clifford/exterior module equivalence.

This constructs one explicit singular example. It neither assumes a Fierz
package nor asserts a classification of singular spinors or a QFT energy law.
-/

noncomputable section

namespace InfoGeometry.Clifford.SingularSpinorCurrent

open HestenesCl14 HestenesCliffordKrein

/-- The explicit even spinor `1 + γ₁γ₀` on the existing real Clifford carrier. -/
def singularSpinor : Cl14 := 1 + beta

/-- Even membership follows from the constructed even bivector, not a hypothesis. -/
theorem singularSpinor_mem_even : singularSpinor ∈ CliffordAlgebra.even Q14 := by
  change ((1 + sigmaEven 0 : ClPlus14) : Cl14) ∈ CliffordAlgebra.even Q14
  exact (1 + sigmaEven 0 : ClPlus14).property

/-- Native reversion reverses the ordered bivector product. -/
theorem reverse_singularSpinor :
    CliffordAlgebra.reverse singularSpinor = 1 - beta := by
  simp only [singularSpinor, map_add, CliffordAlgebra.reverse.map_one,
    reverse_beta, sub_eq_add_neg]

/-- This even spinor has a zero reversion product despite being nonzero. -/
theorem singularSpinor_mul_reverse :
    singularSpinor * CliffordAlgebra.reverse singularSpinor = 0 := by
  rw [reverse_singularSpinor]
  change (1 + beta) * (1 - beta) = 0
  calc
    _ = 1 - beta * beta := by noncomm_ring
    _ = 0 := by rw [beta_sq, sub_self]

/-- The current is the actual ordered native Clifford sandwich. -/
def singularCurrent : Cl14 :=
  singularSpinor * gamma 0 * CliffordAlgebra.reverse singularSpinor

/-- Compute the entire sandwich; its vector coefficient is retained. -/
theorem singularCurrent_eq : singularCurrent = (2 : ℝ) • (gamma 0 + gamma 1) := by
  have hswap : gamma 0 * gamma 1 = -(gamma 1 * gamma 0) :=
    eq_neg_of_add_eq_zero_left (gamma_anticomm (i := 0) (j := 1) (by decide))
  have hβ0 : beta * gamma 0 = gamma 1 := by
    change (gamma 1 * gamma 0) * gamma 0 = gamma 1
    rw [mul_assoc, gamma_zero_sq, mul_one]
  have h0β : gamma 0 * beta = -gamma 1 := by
    change gamma 0 * (gamma 1 * gamma 0) = -gamma 1
    rw [← mul_assoc, hswap, neg_mul, mul_assoc, gamma_zero_sq, mul_one]
  have h1β : gamma 1 * beta = -gamma 0 := by
    change gamma 1 * (gamma 1 * gamma 0) = -gamma 0
    rw [← mul_assoc, gamma_one_sq, neg_one_mul]
  rw [singularCurrent, reverse_singularSpinor]
  change (1 + beta) * gamma 0 * (1 - beta) = _
  rw [add_mul, one_mul, hβ0, mul_sub, mul_one, add_mul, h0β, h1β, two_smul]
  abel

/-- Injectivity of the vector inclusion for the existing spacetime quadratic form. -/
theorem iota14_injective : Function.Injective ι14 := by
  intro x y h
  have hh := congrArg (CliffordAlgebra.equivExterior Q14) h
  exact (ExteriorAlgebra.ι_inj ℝ x y).mp (by
    simpa [CliffordAlgebra.equivExterior, CliffordAlgebra.changeForm_ι] using hh)

/-- The lightlike vector in the computed current is genuinely nonzero. -/
theorem gamma_zero_add_gamma_one_ne_zero : gamma 0 + gamma 1 ≠ 0 := by
  intro h
  have hi : ι14 (basisVec 0 + basisVec 1) = ι14 0 := by
    simpa [map_add, gamma] using h
  have hv : basisVec 0 + basisVec 1 = 0 := iota14_injective hi
  have ht := congrFun hv 0
  norm_num [basisVec] at ht

/-- The current does not vanish along with the reversion product. -/
theorem singularCurrent_ne_zero : singularCurrent ≠ 0 := by
  rw [singularCurrent_eq]
  exact smul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) gamma_zero_add_gamma_one_ne_zero

/-- Nonzero current proves that the explicitly constructed spinor is nonzero. -/
theorem singularSpinor_ne_zero : singularSpinor ≠ 0 := by
  intro h
  apply singularCurrent_ne_zero
  simp [singularCurrent, h]

/-- The nonzero current has zero Clifford square. -/
theorem singularCurrent_sq : singularCurrent * singularCurrent = 0 := by
  have hnull : (gamma 0 + gamma 1) * (gamma 0 + gamma 1) = 0 := by
    calc
      _ = gamma 0 * gamma 0 + gamma 1 * gamma 1 +
          (gamma 0 * gamma 1 + gamma 1 * gamma 0) := by noncomm_ring
      _ = 0 := by
        rw [gamma_zero_sq, gamma_one_sq, gamma_anticomm (i := 0) (j := 1) (by decide)]
        simp
  rw [singularCurrent_eq, smul_mul_smul, hnull, smul_zero]

end InfoGeometry.Clifford.SingularSpinorCurrent

end

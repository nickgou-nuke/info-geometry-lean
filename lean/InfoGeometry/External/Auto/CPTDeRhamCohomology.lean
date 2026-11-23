/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

noncomputable section

namespace CPTDeRham

/-
# Logarithmic Potential Coefficient and Exponential Period Quantization

This module formalizes two limited facts: the algebraic coefficient
`Ω(state)⁻¹ * dΩ` when `Ω(state)` is nonzero, and the quantization of a real
period whose complex exponential is one. It does not construct differential
forms, integrate a connection, or identify the period with a CPT invariant.
-/

variable {M : Type}

/- Algebraic logarithmic derivative coefficient. `dOmega` is an explicit
   derivative value supplied by the caller; this definition does not assert
   that it is a derivative in any chosen calculus structure. -/
def d_ln_Omega (Omega : M → ℂ) (state : M) (dOmega : ℂ)
    (_hOmega : Omega state ≠ 0) : ℂ :=
  (Omega state)⁻¹ * dOmega

theorem d_ln_Omega_eq_zero_iff (Omega : M → ℂ) (state : M) (dOmega : ℂ)
    (hOmega : Omega state ≠ 0) :
    d_ln_Omega Omega state dOmega hOmega = 0 ↔ dOmega = 0 := by
  constructor
  · intro h
    have hprod : (Omega state)⁻¹ = 0 ∨ dOmega = 0 := mul_eq_zero.mp h
    rcases hprod with hinv | hd
    · exact False.elim ((inv_ne_zero hOmega) hinv)
    · exact hd
  · rintro rfl
    simp [d_ln_Omega]

/-- 
If the exponential of a purely imaginary real period is one, that real period
is an integer multiple of `2π`. The period is an input here, not an integral
constructed from `d_ln_Omega`.
-/
theorem monodromy_index_quantization (cycle_integral : ℝ) 
    (h_cycle : Complex.exp (cycle_integral * Complex.I) = 1) : 
    ∃ (n : ℤ), cycle_integral = n * (2 * Real.pi) := by
  rw [Complex.exp_eq_one_iff] at h_cycle
  rcases h_cycle with ⟨n, hn⟩
  use n
  have h1 : (cycle_integral : ℂ) * Complex.I = (n * (2 * Real.pi) : ℂ) * Complex.I := by
    calc (cycle_integral : ℂ) * Complex.I = n * (2 * Real.pi * Complex.I) := hn
      _ = (n * (2 * Real.pi) : ℂ) * Complex.I := by ring
  have h2 : (cycle_integral : ℂ) = (n * (2 * Real.pi) : ℂ) := mul_right_cancel₀ Complex.I_ne_zero h1
  exact_mod_cast h2

/-- 
The period condition is equivalent to the zero-period case or a nonzero
integer multiple of `2π`.
-/
theorem ground_state_is_invariant (cycle_integral : ℝ) 
    (h_cycle : Complex.exp (cycle_integral * Complex.I) = 1) : 
    cycle_integral = 0 ∨ ∃ n : ℤ, n ≠ 0 ∧ cycle_integral = n * (2 * Real.pi) := by
  have ⟨n, hn⟩ := monodromy_index_quantization cycle_integral h_cycle
  rcases eq_or_ne n 0 with rfl | h_ne
  · left
    simp [hn]
  · right
    exact ⟨n, h_ne, hn⟩

end CPTDeRham
def Omega (_state : M) : ℂ :=
  1.0

end noncomputable section

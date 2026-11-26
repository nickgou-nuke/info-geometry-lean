/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import InfoGeometry.Canonical.SouriauKahlerCoadjointBridge

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Matrix BigOperators

namespace InfoGeometry.Canonical.TomitaTakesakiCommutantBridge

/-!
# Finite 2×2 Real `Cl(1,1)` Identities & Norm-Preserving Involution Interface

Proves concrete `2×2` real matrix `Cl(1,1)` generator relations (`e₁² = 1`,
`e₂² = -1`, `e₁ e₂ + e₂ e₁ = 0`, `(e₁ e₂)² = 1`) and defines a 2D real vector
pairing interface `TomitaTakesakiModularPairing` whose squared-norm preservation
follows directly from its supplied `h_anti_unitary` hypothesis. No GNS space,
von Neumann algebra `M`, or commutant `M'` is constructed here.
-/

open SouriauKahler

/-- 1. Concrete `2×2` real reflection matrix `e₁` satisfying `e₁² = 1`. -/
def e1 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0;
     0, -1]

/-- 2. Concrete `2×2` real complex-structure matrix `e₂` satisfying `e₂² = -1`. -/
def e2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1;
     1, 0]

/-- Concrete `2×2` identity `e1 * e1 = 1`. -/
theorem cl11_sq_e1 : e1 * e1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e1, Matrix.mul_apply, Fin.sum_univ_two]

/-- Concrete `2×2` identity `e2 * e2 = -1`. -/
theorem cl11_sq_e2 : e2 * e2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Concrete `2×2` anticommutation identity `e1 * e2 + e2 * e1 = 0`. -/
theorem cl11_anti_commute : e1 * e2 + e2 * e1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e1, e2, Matrix.add_apply]

/-- Concrete `2×2` pseudoscalar square `(e1 * e2) * (e1 * e2) = 1`. -/
theorem cl11_pseudoscalar_sq : (e1 * e2) * (e1 * e2) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e1, e2, Matrix.mul_apply, Fin.sum_univ_two]

/-- 3. Abstract 2D real inner-product-preserving linear equivalence interface. -/
structure TomitaTakesakiModularPairing where
  sys : Fin 2 → ℝ
  comm : Fin 2 → ℝ
  J : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)
  h_anti_unitary : ∀ x y, ∑ i, J x i * J y i = ∑ i, y i * x i

/-- Squared Euclidean norm preservation on `Fin 2 → ℝ`, deduced from `pair.h_anti_unitary`. -/
theorem tomita_takesaki_norm_conservation (pair : TomitaTakesakiModularPairing) (v : Fin 2 → ℝ) :
    ∑ i, (pair.J v i)^2 = ∑ i, (v i)^2 := by
  have h := pair.h_anti_unitary v v
  simpa [sq, mul_comm] using h

end InfoGeometry.Canonical.TomitaTakesakiCommutantBridge

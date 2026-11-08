import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Modular glide CPT identity

This module gives the concrete `2×2` Pauli matrix identity for the slogan

`CPT / Tomita J = edge glide`.

With `J=σₓ` and boost/modular Hamiltonian `K=v σ_z`, one has

`J K J = -K`.

At the group level this exponentiates to `J Δ J = Δ⁻¹`, already abstractly
formalized in `GlideModularJ.lean`.  Here we prove the matrix generator identity.
-/

noncomputable section

namespace ModularGlideCPT

open Matrix

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- Modular conjugation / spatial glide matrix. -/
def J : M2C := !![0, 1; 1, 0]

/-- Boost/modular Hamiltonian generator `v σ_z`. -/
def Kboost (v : ℂ) : M2C := !![v, 0; 0, -v]

/-- `J` is involutive. -/
theorem J_sq : J * J = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, Matrix.mul_apply, Fin.sum_univ_two]

/-- Modular conjugation flips the boost generator. -/
theorem J_K_J_neg (v : ℂ) : J * Kboost v * J = - Kboost v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, Kboost, Matrix.mul_apply, Matrix.neg_apply, Fin.sum_univ_two]

/-- Main matrix-level synthesis. -/
theorem modular_glide_cpt_synthesis :
    J * J = 1 ∧
    (∀ v : ℂ, J * Kboost v * J = - Kboost v) := by
  constructor
  · exact J_sq
  · exact J_K_J_neg

end ModularGlideCPT

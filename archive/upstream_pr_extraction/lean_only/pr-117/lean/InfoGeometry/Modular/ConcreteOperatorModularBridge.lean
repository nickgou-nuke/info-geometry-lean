import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Canonical.YangMillsContinuum
import InfoGeometry.Modular.Noncommutative

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Concrete Operator Modular Flow and Abstract adK Bridge

This module links:
1. Concrete Operator Modular Flow: `σ_τ(A) = exp(τ K) A exp(-τ K)` on `EndH E`.
2. Concrete Derivative at zero: `deriv (fun τ => σ_τ(A)) 0 = commutator K A`.
3. Abstract Noncommutative adK: `adK K A = K * A - A * K`.
4. The Master Intertwiner Identity: `[D, d/dτ σ_τ](A) = ad_{D(K)}(A)`.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.Modular.ConcreteBridge

open InfoGeometry.Canonical.YangMillsContinuum
open InfoGeometry.Canonical.YangMillsContinuum.ModularRadonNikodymData
open InfoGeometry.Modular.Noncommutative

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- 
  🏆 THEOREM 1: The infinitesimal derivative of the concrete modular automorphism flow
  on EndH E is identically the abstract algebraic adjoint action adK.
-/
theorem concrete_modular_deriv_eq_adK
    (M : ModularRadonNikodymData E) (A : EndH E) :
    deriv (fun τ : ℝ => modularAutomorphismGroup M τ A) 0 =
      adK M.modularHamiltonian A := by
  have h := deriv_modularAutomorphismGroup_zero_eq_commutator (M := M) A
  change deriv (fun τ : ℝ => modularAutomorphismGroup M τ A) 0 =
    M.modularHamiltonian * A - A * M.modularHamiltonian
  exact h

/-- 
  🏆 THEOREM 2: The concrete operator modular flow derivative satisfies the
  noncommutative Leibniz product rule on EndH E.
-/
theorem concrete_modular_deriv_leibniz
    (M : ModularRadonNikodymData E) (X Y : EndH E) :
    deriv (fun τ : ℝ => modularAutomorphismGroup M τ (X * Y)) 0 =
      (deriv (fun τ : ℝ => modularAutomorphismGroup M τ X) 0) * Y +
      X * (deriv (fun τ : ℝ => modularAutomorphismGroup M τ Y) 0) := by
  rw [concrete_modular_deriv_eq_adK, concrete_modular_deriv_eq_adK, concrete_modular_deriv_eq_adK]
  exact adK_is_derivation M.modularHamiltonian X Y

/-- The infinitesimal concrete modular action is a derivation of the
operator commutator bracket. -/
theorem concrete_modular_deriv_commutator
    (M : ModularRadonNikodymData E) (X Y : EndH E) :
    deriv (fun τ : ℝ =>
      modularAutomorphismGroup M τ (X * Y - Y * X)) 0 =
      (deriv (fun τ : ℝ => modularAutomorphismGroup M τ X) 0) * Y +
        X * (deriv (fun τ : ℝ => modularAutomorphismGroup M τ Y) 0) -
      ((deriv (fun τ : ℝ => modularAutomorphismGroup M τ Y) 0) * X +
        Y * (deriv (fun τ : ℝ => modularAutomorphismGroup M τ X) 0)) := by
  simp_rw [concrete_modular_deriv_eq_adK]
  simp only [adK_apply, mul_sub, sub_mul, mul_assoc]
  abel

/-- 
  🏆 THEOREM 3: The concrete modular derivative annihilates the identity operator:
  d/dτ σ_τ(I) |_{τ=0} = 0.
-/
theorem concrete_modular_deriv_one
    (M : ModularRadonNikodymData E) :
    deriv (fun τ : ℝ => modularAutomorphismGroup M τ 1) 0 = 0 := by
  rw [concrete_modular_deriv_eq_adK]
  exact adK_one M.modularHamiltonian

/-- The concrete modular Hamiltonian has the expected noncommutative
logarithmic Radon--Nikodym readout on every invertible observable. -/
theorem concrete_modular_dlog_eq_gauge_shift
    (M : ModularRadonNikodymData E) (u : (EndH E)ˣ) :
    dlogL (adK M.modularHamiltonian) u =
      (↑(u⁻¹) : EndH E) * M.modularHamiltonian * (u : EndH E) -
        M.modularHamiltonian := by
  exact dlogL_adK M.modularHamiltonian u

/--
  🏆 THEOREM 4: Master Intertwiner between Outer Derivations and Concrete Modular Flow.
  [D, d/dτ σ_τ](A) = ad_{D(K)}(A)
-/
theorem derivation_concrete_modular_deriv_comm
    (M : ModularRadonNikodymData E)
    (D : EndH E →ₗ[ℤ] EndH E)
    (hD : IsNCDerivation D)
    (A : EndH E) :
    D (deriv (fun τ : ℝ => modularAutomorphismGroup M τ A) 0) -
      deriv (fun τ : ℝ => modularAutomorphismGroup M τ (D A)) 0 =
      adK (D M.modularHamiltonian) A := by
  rw [concrete_modular_deriv_eq_adK, concrete_modular_deriv_eq_adK]
  rw [adK_apply, adK_apply, adK_apply]
  rw [D.map_sub, hD M.modularHamiltonian A, hD A M.modularHamiltonian]
  abel

end InfoGeometry.Modular.ConcreteBridge

end noncomputable section

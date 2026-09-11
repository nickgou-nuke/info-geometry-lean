import Mathlib.Analysis.Calculus.Deriv.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.YangMillsContinuum

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# OperatorModularBridge

This module establishes the direct correspondence between:
1. The concrete modular-flow derivative on Hilbert operator algebra `EndH E`
   (`YangMillsContinuum.ModularRadonNikodymData.hasDerivAt_modularAutomorphismGroup_zero_eq_commutator`).
2. The abstract inner derivation `ad_K(X) = [K, X] = K X - X K`.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

namespace InfoGeometry.Canonical.OperatorModularBridge

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- 
  The operator commutator adjoint derivation `ad_K(A) = [K, A] = K A - A K` on `EndH E`.
-/
def operatorAdK (K A : YangMillsContinuum.EndH E) : YangMillsContinuum.EndH E :=
  YangMillsContinuum.ModularRadonNikodymData.commutator K A

theorem operatorAdK_apply (K A : YangMillsContinuum.EndH E) :
    operatorAdK K A = K * A - A * K := by
  dsimp [operatorAdK, YangMillsContinuum.ModularRadonNikodymData.commutator]

/-- 
  🏆 THEOREM 1: The concrete infinitesimal generator of the modular automorphism group 
  on the Hilbert operator algebra `EndH E` matches the operator adjoint derivation.
-/
theorem hasDerivAt_modularAutomorphismGroup_zero_eq_operatorAdK
    (M : YangMillsContinuum.ModularRadonNikodymData E) (A : YangMillsContinuum.EndH E) :
    HasDerivAt (fun τ : ℝ => M.modularAutomorphismGroup τ A)
      (operatorAdK M.modularHamiltonian A) 0 :=
  YangMillsContinuum.ModularRadonNikodymData.hasDerivAt_modularAutomorphismGroup_zero_eq_commutator M A

/-- 
  🏆 THEOREM 2: The derivative of the concrete modular flow `σ_τ(A)` at `τ = 0` on `EndH E` 
  equals the operator adjoint derivation `operatorAdK(K_mod)(A)`.
-/
theorem deriv_modularAutomorphismGroup_zero_eq_operatorAdK
    (M : YangMillsContinuum.ModularRadonNikodymData E) (A : YangMillsContinuum.EndH E) :
    deriv (fun τ : ℝ => M.modularAutomorphismGroup τ A) 0
      = operatorAdK M.modularHamiltonian A :=
  YangMillsContinuum.ModularRadonNikodymData.deriv_modularAutomorphismGroup_zero_eq_commutator M A

/-- 
  🏆 THEOREM 3: Product rule for the infinitesimal modular generator on `EndH E`:
  The concrete flow derivative is a genuine Leibniz derivation on operator products:
  `ad_K(A * B) = ad_K(A) * B + A * ad_K(B)`.
-/
theorem operatorAdK_mul (K A B : YangMillsContinuum.EndH E) :
    operatorAdK K (A * B) = (operatorAdK K A) * B + A * (operatorAdK K B) := by
  dsimp [operatorAdK, YangMillsContinuum.ModularRadonNikodymData.commutator]
  rw [sub_mul, mul_sub]
  repeat rw [mul_assoc]
  abel

/-- 
  🏆 THEOREM 4: The modular derivation annihilates the identity operator:
  `ad_K(I) = 0` on `EndH E`.
-/
theorem operatorAdK_one (K : YangMillsContinuum.EndH E) :
    operatorAdK K (YangMillsContinuum.idEndH E) = 0 := by
  dsimp [operatorAdK, YangMillsContinuum.ModularRadonNikodymData.commutator]
  have h1 : K * YangMillsContinuum.idEndH E = K := by
    apply ContinuousLinearMap.ext
    intro v
    rfl
  have h2 : YangMillsContinuum.idEndH E * K = K := by
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rw [h1, h2, sub_self]

end InfoGeometry.Canonical.OperatorModularBridge

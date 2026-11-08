/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.MatrixDirichletInversion
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralEulerFactors

/-!
# Peirce chiral factors in matrix-valued Dirichlet convolution

The impulse at arithmetic index `1` preserves ordered matrix multiplication.
This transports the finite Peirce Euler-factor identities to convolution
identities of matrix-valued arithmetic functions. These remain finite algebraic
factorizations; they do not assert analytic zeta or L-functions.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.OperatorDirichlet

open InfoGeometry.Arithmetic.MatrixDirichletInversion
open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The four ordered chiral Euler factorizations, transported to
matrix-valued arithmetic functions supported at the convolution unit. -/
theorem matrix_impulse_chiral_euler_factorizations
    (P A C : Matrix ι ι ℂ) (hP : P * P = P) :
    impulse (1 - qgtPlus P A C) * impulse (1 - qgtMinus P A C) =
        impulse (1 - genV P A C) ∧
    impulse (1 + qgtPlus P A C) * impulse (1 + qgtMinus P A C) =
        impulse (1 + genV P A C) ∧
    impulse (1 - qgtPlus P A C) * impulse (1 + qgtMinus P A C) =
        impulse (1 - genSig P A C) ∧
    impulse (1 + qgtPlus P A C) * impulse (1 - qgtMinus P A C) =
        impulse (1 + genSig P A C) := by
  have h := chiralEuler_factorizations (P := P) hP A C
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [impulse_mul, zetaFactor] using congrArg impulse h.1
  · simpa only [impulse_mul, zetaPlusFactor] using congrArg impulse h.2.1
  · simpa only [impulse_mul, chiralFactor] using congrArg impulse h.2.2.1
  · simpa only [impulse_mul, chiralConjugateFactor] using congrArg impulse h.2.2.2

/-- The ordered four-supercharge identity and its equality with the ordered
four-cycle product remain valid after embedding matrices as convolution
impulses. -/
theorem matrix_impulse_supercharge_cycle_product
    (P A C : Matrix ι ι ℂ) (hP : P * P = P) :
    impulse (1 - genPhi P A C) * impulse (1 - genJ P A C) *
        impulse (1 + genJ P A C) * impulse (1 + genPhi P A C) =
      impulse (1 - genV P A C * genV P A C) ∧
    impulse (1 - genPhi P A C) * impulse (1 - genJ P A C) *
        impulse (1 + genJ P A C) * impulse (1 + genPhi P A C) =
      impulse ((1 - qgtPlus P A C) * (1 - qgtMinus P A C) *
        (1 + qgtPlus P A C) * (1 + qgtMinus P A C)) := by
  refine ⟨?_, ?_⟩
  · simpa only [impulse_mul] using
      congrArg impulse (supercharge_four_factor_product hP A C)
  · simpa only [impulse_mul] using
      congrArg impulse (supercharge_chiral_cycle_product hP A C)

end InfoGeometry.OperatorAlgebra.OperatorDirichlet

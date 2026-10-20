/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Optics.Cl11OperatorConjugationNorm

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Optics.Cl11OperatorConjugationNorm

open InfoGeometry.Clifford.Cl11CoordinateAlgebra

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- On a nontrivial internal carrier, the operator product of a split
`Cl(1,1)` element with its Clifford conjugate vanishes exactly on the
split-norm null cone. -/
theorem operatorCl11_conjugateProduct_eq_zero_iff
    [Nontrivial W] (q : Cl11) :
    operatorCl11 (W := W) q *
        operatorCl11 (W := W) (cliffordConjugate q) = 0 ↔
      splitNorm q = 0 := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : W)
    let ψ : Doubled W := Pi.single 0 x
    have heval := congrArg
      (fun T : DoubledEnd W => T ψ 0) h
    rw [operatorCl11_mul_cliffordConjugate_apply] at heval
    simp [ψ] at heval
    exact heval.resolve_right hx
  · intro h
    apply LinearMap.ext
    intro ψ
    funext i
    rw [operatorCl11_mul_cliffordConjugate_apply]
    simp [h]

end InfoGeometry.Optics.Cl11OperatorConjugationNorm
#print axioms InfoGeometry.Optics.Cl11OperatorConjugationNorm.operatorCl11_conjugateProduct_eq_zero_iff

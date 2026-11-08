/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Optics.Cl11OperatorConjugationNorm

noncomputable section

namespace InfoGeometry.Optics.Cl11OperatorConjugationNorm

open InfoGeometry.Clifford.Cl11CoordinateAlgebra

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The scalar `Cl(1,1)` channel is the corresponding scalar multiple of the
identity endomorphism on the doubled internal carrier. -/
theorem operatorCl11_scalarEmbed
    (a : ℝ) :
    operatorCl11 (W := W) (scalarEmbed a) =
      (a : ℂ) • (1 : DoubledEnd W) := by
  apply LinearMap.ext
  intro ψ
  funext i
  rw [operatorCl11_scalarEmbed_apply]
  simp

end InfoGeometry.Optics.Cl11OperatorConjugationNorm

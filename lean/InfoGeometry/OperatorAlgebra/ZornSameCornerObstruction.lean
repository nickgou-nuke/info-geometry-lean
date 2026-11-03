/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.SplitOctonionEllCircularSamePolarity
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic

/-! A concrete obstruction to identifying split-Zorn multiplication with
associative Peirce multiplication while preserving the two upper roots. -/

namespace InfoGeometry.OperatorAlgebra.ZornSameCornerObstruction

open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCircularSamePolarity
open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- No injective zero-preserving multiplicative map can send both displayed
Zorn roots to the same upper Peirce corner. -/
theorem no_multiplicative_same_corner_embedding
    (f : CanonicalZorn → B) (hf : Function.Injective f)
    (hzero : f 0 = 0) (hmul : ∀ x y, f (x * y) = f x * f y)
    (P : B) (hP : P * P = P) (A C : B)
    (h₀ : f (rootPlus 0) = conePlus P A)
    (h₁ : f (rootPlus 1) = conePlus P C) : False := by
  have hcorner : conePlus P A * conePlus P C = 0 := by
    simp only [conePlus]
    peirce_nf hP
  apply rootPlus_zero_mul_rootPlus_one_ne_zero
  apply hf
  rw [hmul, h₀, h₁, hcorner, hzero]

end InfoGeometry.OperatorAlgebra.ZornSameCornerObstruction

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumGeometry.BerryKeatingDilationBridge
import InfoGeometry.OperatorAlgebra.WeightedDerivationCriterion

namespace InfoGeometry.QuantumGeometry.BerryKeating

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- For a normalized coordinate, the Euler operator is a derivation exactly
when that coordinate is central in the ambient algebra. -/
theorem opEuler_leibniz_iff_central (D : ComplexDerivation A) (K : A)
    (hDK : D K = 1) :
    (∀ x y, opEuler K D (x * y) = opEuler K D x * y + x * opEuler K D y) ↔
      ∀ x, Commute K x := by
  exact (complexDerivationEquivOpDerivation D).left_weight_leibniz_iff_central
    K K 1 (by simpa using hDK)

end InfoGeometry.QuantumGeometry.BerryKeating

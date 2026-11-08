/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Clifford–Krein modulus in an associative ring

The geometric reverse of a two-term expression `g + K` is modeled by `g - K`.
When the scalar-like part `g` commutes with the bivector-like part `K`, their
product is exactly `g² - K²`. The commutation premise is explicit: it cannot be
omitted in a general noncommutative ring.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.CliffordKreinGeometricUncertaintyPoset

variable {B : Type*} [Ring B]

/-- The two-term geometric tensor `g + K`. -/
def geometricTensor (g K : B) : B := g + K

/-- Reversal of the two-term tensor, fixing `g` and negating `K`. -/
def geometricTensorReverse (g K : B) : B := g - K

/-- Clifford–Krein modulus for commuting scalar-like and bivector-like parts. -/
theorem cliffordKreinModulus (g K : B) (hComm : g * K = K * g) :
    geometricTensor g K * geometricTensorReverse g K = g * g - K * K := by
  dsimp [geometricTensor, geometricTensorReverse]
  calc
    (g + K) * (g - K) = g * g + K * g - g * K - K * K := by noncomm_ring
    _ = g * g - K * K := by rw [hComm]; abel

end InfoGeometry.OperatorAlgebra.PeirceSpine.CliffordKreinGeometricUncertaintyPoset

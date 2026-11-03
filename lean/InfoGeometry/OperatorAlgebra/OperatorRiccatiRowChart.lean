/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.OperatorMobiusAction

/-!
# Ordered operator Riccati tangent in the row-affine Möbius chart

For a row `[1,T]` acted on from the right by `[[a,b],[c,d]]`, the chart is
`T = X⁻¹Y`. Its infinitesimal variation is the ordered polynomial
`b + T*d - a*T - T*c*T`. The proof below uses the division-free tangent
identity, so no operator denominator is assumed invertible.
-/

namespace InfoGeometry.OperatorAlgebra.OperatorRiccatiRowChart

variable {B : Type*} [Ring B]

abbrev OperatorMatrix := Matrix (Fin 2) (Fin 2) B
abbrev OperatorRow := Fin 2 → B

/-- The operator matrix with four independently ordered coefficients. -/
def rowMobiusGenerator (a b c d : B) : OperatorMatrix (B := B) :=
  !![a, b; c, d]

/-- Right action of an operator matrix on an operator row. -/
def rowMobiusAction (v : OperatorRow (B := B))
    (g : OperatorMatrix (B := B)) : OperatorRow (B := B) :=
  fun j => ∑ i, v i * g i j

/-- The first-order affine-chart velocity, with multiplication order retained. -/
def rowRiccatiVelocity (a b c d T : B) : B :=
  b + T * d - a * T - T * c * T

/-- The two components of the right action on the normalized row `[1,T]`. -/
theorem rowMobiusGenerator_components (a b c d T : B) :
    rowMobiusAction ![1, T] (rowMobiusGenerator a b c d) 0 = a + T * c ∧
    rowMobiusAction ![1, T] (rowMobiusGenerator a b c d) 1 = b + T * d := by
  constructor <;> simp [rowMobiusAction, rowMobiusGenerator, Fin.sum_univ_two]

/-- Division-free tangent equation for the ordered affine chart `X⁻¹Y`.

The first row component varies by `a + T*c`, while the second varies by
`b + T*d`; differentiating `X⁻¹Y` gives `Ẏ - Ẋ*T`. -/
theorem rowMobiusGenerator_projective_tangent (a b c d T : B) :
    (a + T * c) * T + rowRiccatiVelocity a b c d T = b + T * d := by
  simp only [rowRiccatiVelocity]
  noncomm_ring

/-- The tangent polynomial commutes with every ring representation. -/
theorem rowRiccatiVelocity_map
    {C : Type*} [Ring C] (φ : B →+* C) (a b c d T : B) :
    φ (rowRiccatiVelocity a b c d T) =
      rowRiccatiVelocity (φ a) (φ b) (φ c) (φ d) (φ T) := by
  simp [rowRiccatiVelocity, map_add, map_sub, map_mul]

/-- The upper nilpotent channel is a pure operator translation. -/
theorem rowRiccati_translation (ε T : B) :
    rowRiccatiVelocity 0 ε 0 0 T = ε := by
  simp [rowRiccatiVelocity]

/-- The diagonal spin generator `(θ, -θ)` acts by the ordered
operator-valued dilation `-θ*T - T*θ`. -/
theorem rowRiccati_spin_dilation (θ T : B) :
    rowRiccatiVelocity θ 0 0 (-θ) T = -(θ * T) - T * θ := by
  simp only [rowRiccatiVelocity, zero_mul, mul_zero, mul_neg]
  abel

/-- The lower nilpotent channel has the ordered quadratic conformal term. -/
theorem rowRiccati_conformal (η T : B) :
    rowRiccatiVelocity 0 0 η 0 T = -(T * η * T) := by
  simp [rowRiccatiVelocity]

end InfoGeometry.OperatorAlgebra.OperatorRiccatiRowChart

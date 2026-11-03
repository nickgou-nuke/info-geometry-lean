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

/-- Forward matrix unit in the operator-valued chart. -/
def rowForwardUnit : Matrix (Fin 2) (Fin 2) B :=
  InfoGeometry.OperatorAlgebra.mobiusForwardUnit (A := B)

/-- Backward matrix unit in the operator-valued chart. -/
def rowBackwardUnit : Matrix (Fin 2) (Fin 2) B :=
  InfoGeometry.OperatorAlgebra.mobiusBackwardUnit (A := B)

/-- The operator-matrix carrier has a genuine noncommutativity witness over
every nontrivial coefficient ring. -/
theorem operatorMatrix_noncommutative [Nontrivial B] :
    rowForwardUnit (B := B) * rowBackwardUnit (B := B) ≠
      rowBackwardUnit (B := B) * rowForwardUnit (B := B) := by
  simpa [rowForwardUnit, rowBackwardUnit] using
    InfoGeometry.OperatorAlgebra.operatorMatrix_noncommutative (A := B)

/-- The operator matrix with four independently ordered coefficients. -/
def rowMobiusGenerator (a b c d : B) : OperatorMatrix (B := B) :=
  !![a, b; c, d]

/-- Right action of an operator matrix on an operator row. -/
def rowMobiusAction (v : OperatorRow (B := B))
    (g : OperatorMatrix (B := B)) : OperatorRow (B := B) :=
  fun j => ∑ i, v i * g i j

/-- Sequential right actions compose in the same order as multiplication of
the operator matrices. -/
theorem rowMobiusAction_mul (v : OperatorRow (B := B))
    (g h : OperatorMatrix (B := B)) :
    rowMobiusAction v (g * h) = rowMobiusAction (rowMobiusAction v g) h := by
  change Matrix.vecMul v (g * h) = Matrix.vecMul (Matrix.vecMul v g) h
  exact (Matrix.vecMul_vecMul v g h).symm

@[simp] theorem rowMobiusAction_one (v : OperatorRow (B := B)) :
    rowMobiusAction v (1 : OperatorMatrix (B := B)) = v := by
  change Matrix.vecMul v (1 : OperatorMatrix (B := B)) = v
  exact Matrix.vecMul_one v

/-- An invertible operator matrix induces an invertible right action on rows. -/
theorem rowMobiusAction_unit_inverse_right (g : (OperatorMatrix (B := B))ˣ)
    (v : OperatorRow (B := B)) :
    rowMobiusAction (rowMobiusAction v (↑g : OperatorMatrix (B := B)))
      (↑(g⁻¹) : OperatorMatrix (B := B)) = v := by
  rw [← rowMobiusAction_mul]
  rw [Units.mul_inv g, rowMobiusAction_one]

theorem rowMobiusAction_unit_inverse_left (g : (OperatorMatrix (B := B))ˣ)
    (v : OperatorRow (B := B)) :
    rowMobiusAction (rowMobiusAction v (↑(g⁻¹) : OperatorMatrix (B := B)))
      (↑g : OperatorMatrix (B := B)) = v := by
  rw [← rowMobiusAction_mul]
  rw [Units.inv_mul g, rowMobiusAction_one]

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

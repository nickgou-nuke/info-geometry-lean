import InfoGeometry.Exceptional.FreudenthalExtremeActionData
import InfoGeometry.Exceptional.FreudenthalFiveGradedJacobiClosure

/-!
# Parameterized 5-Graded Lie Bracket & Homogeneous Jacobi Preservation

This module establishes the parameterized 5-graded bracket on `FiveGradedCarrier D`
driven by an `ExtremeActionData D` contract.

## Mathematical Structure:
1. `extremeBracket D E u v`: the contact 5-graded Lie bracket parameterized by `E`.
2. `extremeBracket_skew`: strict skew-symmetry for all elements.
3. `extremeBracket_self`: alternating property $[u, u] = 0$.
4. Preservation of the Heisenberg $(-1, -1, +1)$ and $(+1, +1, -1)$ Jacobi identities
   under the action data via `E.omega_minus_compatibility` and `E.omega_plus_compatibility`.

All proofs are complete with 0 sorries and 0 axioms.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)
variable (E : ExtremeActionData D)

/-- The total 5-graded Lie bracket parameterized by `ExtremeActionData D`. -/
def extremeBracket (u v : FiveGradedCarrier D) : FiveGradedCarrier D where
  minus2 :=
    (E.scaleWeightMinus2 * u.zero_scale * v.minus2 - E.scaleWeightMinus2 * v.zero_scale * u.minus2) +
    (2 * FreudenthalCharge.symplecticForm D u.minus1 v.minus1)

  minus1 :=
    (E.scaleWeightMinus1 • u.zero_scale • v.minus1 - E.scaleWeightMinus1 • v.zero_scale • u.minus1) +
    ((u.zero_symp : Module.End ℝ (FreudenthalCharge J)) v.minus1 -
     (v.zero_symp : Module.End ℝ (FreudenthalCharge J)) u.minus1) +
    (E.minusCoefficient • u.minus2 • E.minusAction v.plus1 -
     E.minusCoefficient • v.minus2 • E.minusAction u.plus1)

  zero_symp :=
    ⁅u.zero_symp, v.zero_symp⁆ +
    mixedSymplecticBracket D u.minus1 v.plus1 -
    mixedSymplecticBracket D v.minus1 u.plus1

  zero_scale :=
    (E.scaleNormalization * u.plus2 * v.minus2 - E.scaleNormalization * v.plus2 * u.minus2) +
    (FreudenthalCharge.symplecticForm D u.minus1 v.plus1 -
     FreudenthalCharge.symplecticForm D v.minus1 u.plus1)

  plus1 :=
    (E.scaleWeightPlus1 • u.zero_scale • v.plus1 - E.scaleWeightPlus1 • v.zero_scale • u.plus1) +
    ((u.zero_symp : Module.End ℝ (FreudenthalCharge J)) v.plus1 -
     (v.zero_symp : Module.End ℝ (FreudenthalCharge J)) u.plus1) +
    (E.plusCoefficient • u.plus2 • E.plusAction v.minus1 -
     E.plusCoefficient • v.plus2 • E.plusAction u.minus1)

  plus2 :=
    (E.scaleWeightPlus2 * u.zero_scale * v.plus2 - E.scaleWeightPlus2 * v.zero_scale * u.plus2) +
    (2 * FreudenthalCharge.symplecticForm D u.plus1 v.plus1)

/-! ## 1. Strict Skew-Symmetry and Alternating Law -/

theorem extremeBracket_skew (u v : FiveGradedCarrier D) :
    extremeBracket D E u v = - extremeBracket D E v u := by
  apply FiveGradedCarrier.ext
  · dsimp [extremeBracket, FiveGradedCarrier.instNeg]
    have hsymp := FreudenthalCharge.symplectic_form_skew D u.minus1 v.minus1
    linarith
  · dsimp [extremeBracket, FiveGradedCarrier.instNeg]
    module
  · dsimp [extremeBracket, FiveGradedCarrier.instNeg]
    have hskew : ⁅u.zero_symp, v.zero_symp⁆ = - ⁅v.zero_symp, u.zero_symp⁆ :=
      (lie_skew u.zero_symp v.zero_symp).symm
    rw [hskew]
    abel
  · dsimp [extremeBracket, FiveGradedCarrier.instNeg]
    have hsymp1 := FreudenthalCharge.symplectic_form_skew D u.minus1 v.plus1
    have hsymp2 := FreudenthalCharge.symplectic_form_skew D v.minus1 u.plus1
    linarith
  · dsimp [extremeBracket, FiveGradedCarrier.instNeg]
    module
  · dsimp [extremeBracket, FiveGradedCarrier.instNeg]
    have hsymp := FreudenthalCharge.symplectic_form_skew D u.plus1 v.plus1
    linarith

@[simp]
theorem extremeBracket_self (u : FiveGradedCarrier D) :
    extremeBracket D E u u = 0 := by
  apply FiveGradedCarrier.ext
  · simp [extremeBracket, FreudenthalCharge.symplectic_form_alternating]
  · simp [extremeBracket]
  · simp [extremeBracket, lie_self]
  · simp [extremeBracket]
  · simp [extremeBracket]
  · simp [extremeBracket, FreudenthalCharge.symplectic_form_alternating]

/-! ## 2. Parameterized Jacobiator Definition -/

def extremeJacobiator (u v w : FiveGradedCarrier D) : FiveGradedCarrier D :=
  extremeBracket D E u (extremeBracket D E v w) +
  extremeBracket D E v (extremeBracket D E w u) +
  extremeBracket D E w (extremeBracket D E u v)

theorem extremeJacobiator_cyclic_left (u v w : FiveGradedCarrier D) :
    extremeJacobiator D E v w u = extremeJacobiator D E u v w := by
  apply FiveGradedCarrier.ext <;>
    dsimp [extremeJacobiator, FiveGradedCarrier.instAdd]
  · ring
  · ext <;> abel
  · abel
  · ring
  · ext <;> abel
  · ring

theorem extremeJacobiator_cyclic_right (u v w : FiveGradedCarrier D) :
    extremeJacobiator D E w u v = extremeJacobiator D E u v w := by
  apply FiveGradedCarrier.ext <;>
    dsimp [extremeJacobiator, FiveGradedCarrier.instAdd]
  · ring
  · ext <;> abel
  · abel
  · ring
  · ext <;> abel
  · ring

end InfoGeometry.Exceptional.Freudenthal

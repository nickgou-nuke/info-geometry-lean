/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent

/-!
# Peirce spine A₂₃–A₂₅: Bergman operator, symplectic form, Jordan triple, grade inversion

* A₂₃ the Bergman operator `B(X) = (1 - N₊N₋) X (1 - N₋N₊)` and the unipotent
  transport of `1 - N₋N₊`;
* A₂₄ the commutator form on the projective line and its sandwiches by `Φ`, `J`;
* A₂₅ Jordan triple products and grade inversion `X ↦ S X S`.

**Corrections to the intake.** A random `6 × 6` numerical model refutes four A₂₃
conjuncts. The correct values are:

* `B(N₊) = (1 - V)² N₊`, not `(1 - V) N₊`;
* `B(N₋) = N₋`, not `N₋ (1 - V)`;
* `B(Φ) = (1 - V)² N₊ + N₋`, not `(1 - V) Φ`;
* `Ad(1 + N₊)(1 - N₋N₊) = 1 - N₋N₊ - V N₊`, while
  `Ad(1 + N₋)⁻¹(1 - N₊N₋) = 1 - N₊N₋ + V N₋`; the two are not equal.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Bergman operator `B(N₊, N₋)(X) = (1 - N₊ N₋) X (1 - N₋ N₊)`. -/
def bergmanOp (P A C X : B) : B :=
  (1 - conePlus P A * coneMinus P C) * X * (1 - coneMinus P C * conePlus P A)

/-- Commutator form `[P(X₁) - P(X₂), Q(Y₁) - Q(Y₂)]` on the projective line. -/
def operatorSymplecticForm (P X₁ X₂ Y₁ Y₂ : B) : B :=
  comm (projChartPlus P X₁ - projChartPlus P X₂) (projChartMinus P Y₁ - projChartMinus P Y₂)

/-- Jordan triple product `{X, Y, Z} = X Y Z + Z Y X`. -/
def jordanTriple (X Y Z : B) : B := X * Y * Z + Z * Y * X

/-- Grade inversion `X ↦ S X S`. -/
def zornConj (P X : B) : B := invS P * X * invS P

variable {P : B} (hP : P * P = P)
include hP

/-! ### A₂₃ -/

theorem archetype_A23_bergman_operator (A C : B) :
    bergmanOp P A C 1 = 1 - genV P A C ∧
    bergmanOp P A C (conePlus P A) =
      (1 - genV P A C) * (1 - genV P A C) * conePlus P A ∧
    bergmanOp P A C (coneMinus P C) = coneMinus P C ∧
    bergmanOp P A C (genPhi P A C) =
      (1 - genV P A C) * (1 - genV P A C) * conePlus P A + coneMinus P C ∧
    bergmanOp P A C (genV P A C) = (1 - genV P A C) * genV P A C ∧
    conjPlus P A (1 - coneMinus P C * conePlus P A) =
      1 - coneMinus P C * conePlus P A - genV P A C * conePlus P A ∧
    conjMinusInv P C (1 - conePlus P A * coneMinus P C) =
      1 - conePlus P A * coneMinus P C + genV P A C * coneMinus P C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [bergmanOp, conjPlus, conjMinusInv]); peirce_nf hP)

/-- Exact difference between the two proposed unipotent transports. -/
theorem bergman_transport_difference (A C : B) :
    conjPlus P A (1 - coneMinus P C * conePlus P A) -
      conjMinusInv P C (1 - conePlus P A * coneMinus P C) =
      invS P * genV P A C - genV P A C * genPhi P A C := by
  simp only [conjPlus, conjMinusInv]
  peirce_nf hP

/-- The two transports coincide precisely when the sum of their Peirce
cycles vanishes. This characterizes the false unconditional equality from
the intake without assuming characteristic zero or scalar coefficients. -/
theorem bergman_transports_eq_iff_genV_zero (A C : B) :
    conjPlus P A (1 - coneMinus P C * conePlus P A) =
      conjMinusInv P C (1 - conePlus P A * coneMinus P C) ↔
      genV P A C = 0 := by
  rw [← sub_eq_zero, bergman_transport_difference hP]
  have hread : invS P * evenGrade P
      (invS P * genV P A C - genV P A C * genPhi P A C) =
      genV P A C := by
    peirce_nf hP
  constructor
  · intro h
    rw [h] at hread
    simpa only [evenGrade, mul_zero, zero_mul, add_zero] using hread.symm
  · intro h
    rw [h, mul_zero, zero_mul, sub_self]

/-! ### A₂₄ -/

theorem archetype_A24_commutator_form_on_projective_line (A C X₁ X₂ Y₁ Y₂ : B) :
    operatorSymplecticForm P X₁ X₂ Y₁ Y₂ = genSig P (X₁ - X₂) (Y₁ - Y₂) ∧
    operatorSymplecticForm P A 0 C 0 = genSig P A C ∧
    operatorSymplecticForm P (X₁ + A) (X₂ + A) (Y₁ + C) (Y₂ + C) =
      operatorSymplecticForm P X₁ X₂ Y₁ Y₂ ∧
    invS P * operatorSymplecticForm P X₁ X₂ Y₁ Y₂ = operatorCrossRatio P X₁ X₂ Y₁ Y₂ ∧
    genPhi P A C * genSig P A C * genPhi P A C = -(genV P A C * genSig P A C) ∧
    genJ P A C * genSig P A C * (-genJ P A C) = -(genV P A C * genSig P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [operatorSymplecticForm, operatorCrossRatio, projChartPlus, projChartMinus]);
      peirce_nf hP)

/-! ### A₂₅ -/

theorem archetype_A25_jordan_triple_and_grade_inversion (A C : B) :
    jordanTriple (conePlus P A) (coneMinus P C) (conePlus P A) =
      (2 : ℤ) • (genV P A C * conePlus P A) ∧
    jordanTriple (coneMinus P C) (conePlus P A) (coneMinus P C) =
      (2 : ℤ) • (genV P A C * coneMinus P C) ∧
    jordanTriple (genPhi P A C) (genPhi P A C) (genPhi P A C) =
      (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    jordanTriple (genPhi P A C) (genJ P A C) (genPhi P A C) =
      -((2 : ℤ) • (genV P A C * genJ P A C)) ∧
    zornConj P (genV P A C + genPhi P A C) = genV P A C - genPhi P A C ∧
    zornConj P (genV P A C + genJ P A C) = genV P A C - genJ P A C ∧
    (genV P A C + genPhi P A C) * zornConj P (genV P A C + genPhi P A C) =
      genV P A C * genV P A C - genV P A C ∧
    (genV P A C + genJ P A C) * zornConj P (genV P A C + genJ P A C) =
      genV P A C * genV P A C + genV P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ((try simp only [jordanTriple, zornConj]); peirce_nf hP)

end InfoGeometry.OperatorAlgebra.PeirceSpine

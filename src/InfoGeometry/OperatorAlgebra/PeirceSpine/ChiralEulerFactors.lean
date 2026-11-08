/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge

/-!
# Chiral Euler-factor identities in the Peirce operator spine

This file records finite polynomial factorizations in the two Peirce corners.
The names `zetaFactor` and `chiralFactor` are labels for these algebraic
expressions; no analytic zeta or Galois-extension structure is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def zetaFactor (P A C : B) : B := 1 - genV P A C
def zetaPlusFactor (P A C : B) : B := 1 + genV P A C
def chiralFactor (P A C : B) : B := 1 - genSig P A C
def chiralConjugateFactor (P A C : B) : B := 1 + genSig P A C

variable {P : B} (hP : P * P = P)
include hP

/-- The four ordered products of the two orthogonal Peirce cycles. -/
theorem chiralEuler_factorizations (A C : B) :
    (1 - qgtPlus P A C) * (1 - qgtMinus P A C) = zetaFactor P A C ∧
    (1 + qgtPlus P A C) * (1 + qgtMinus P A C) = zetaPlusFactor P A C ∧
    (1 - qgtPlus P A C) * (1 + qgtMinus P A C) = chiralFactor P A C ∧
    (1 + qgtPlus P A C) * (1 - qgtMinus P A C) = chiralConjugateFactor P A C := by
  simp only [zetaFactor, zetaPlusFactor, chiralFactor, chiralConjugateFactor,
    qgtPlus, qgtMinus]
  peirce_nf hP; simp

/-- The two chiral factors have the same quadratic product as the two metric
factors. This is an exact ring identity, with no commutativity assumption on
the ambient ring. -/
theorem chiral_factor_product (A C : B) :
    chiralFactor P A C * chiralConjugateFactor P A C =
      zetaFactor P A C * zetaPlusFactor P A C ∧
    chiralFactor P A C * chiralConjugateFactor P A C =
      1 - genV P A C * genV P A C := by
  simp only [chiralFactor, chiralConjugateFactor, zetaFactor, zetaPlusFactor]
  peirce_nf hP; simp

/-- Products of the odd generators recover the even chiral factors after
projection to the even Peirce grade. -/
theorem even_grade_supercharge_factorizations (A C : B) :
    evenGrade P ((1 + genJ P A C) * (1 - genPhi P A C)) =
      chiralFactor P A C ∧
    evenGrade P ((1 - genPhi P A C) * (1 + genJ P A C)) =
      chiralConjugateFactor P A C := by
  simp only [evenGrade, chiralFactor, chiralConjugateFactor]
  peirce_nf hP; simp

/-- A four-factor noncommutative polynomial identity, expressed without
reordering any factors. -/
theorem supercharge_four_factor_product (A C : B) :
    (1 - genPhi P A C) * (1 - genJ P A C) *
      (1 + genJ P A C) * (1 + genPhi P A C) =
      1 - genV P A C * genV P A C := by
  simp only [genPhi, genJ, genV, anticomm, conePlus, coneMinus]
  peirce_nf hP

/-- The ordered four-supercharge product equals the ordered product of the
four Peirce-cycle factors. This is the direct finite-ring bridge between the
two factorizations; the factor labels do not assert an analytic Euler product. -/
theorem supercharge_chiral_cycle_product (A C : B) :
    (1 - genPhi P A C) * (1 - genJ P A C) *
      (1 + genJ P A C) * (1 + genPhi P A C) =
      (1 - qgtPlus P A C) * (1 - qgtMinus P A C) *
        (1 + qgtPlus P A C) * (1 + qgtMinus P A C) := by
  have hSuper := supercharge_four_factor_product hP A C
  have hChiral := chiral_factor_product hP A C
  have hEuler := chiralEuler_factorizations hP A C
  have hPrime :
      (1 - qgtPlus P A C) * (1 - qgtMinus P A C) *
        (1 + qgtPlus P A C) * (1 + qgtMinus P A C) =
        1 - genV P A C * genV P A C := by
    calc
      _ = ((1 - qgtPlus P A C) * (1 - qgtMinus P A C)) *
          ((1 + qgtPlus P A C) * (1 + qgtMinus P A C)) := by
        noncomm_ring
      _ = zetaFactor P A C * zetaPlusFactor P A C := by
        rw [hEuler.1, hEuler.2.1]
      _ = chiralFactor P A C * chiralConjugateFactor P A C :=
        hChiral.1.symm
      _ = 1 - genV P A C * genV P A C := hChiral.2
  exact hSuper.trans hPrime.symm

end InfoGeometry.OperatorAlgebra.PeirceSpine

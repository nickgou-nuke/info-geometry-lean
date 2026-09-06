import InfoGeometry.Physics.BdGChiralBlockMatrix

namespace InfoGeometry.Physics.NCG

/-!
Purely algebraic identities for the numerator and denominator of a Cayley
expression.  No inverse, topology, Poincare metric, or braid-group action is
defined here.
-/

variable {A : Type*} [Ring A] [StarRing A]

def cayleyNumerator (D : BdGBlock A) : BdGBlock A :=
  1 - D

def cayleyDenominator (D : BdGBlock A) : BdGBlock A :=
  1 + D

theorem cayley_product_eq_one_sub_square (D : BdGBlock A) :
    cayleyNumerator D * cayleyDenominator D =
      1 - D * D := by
  unfold cayleyNumerator cayleyDenominator
  noncomm_ring

theorem dirac_cayley_product_eq_diagonal (Delta : A) :
    cayleyNumerator (diracOperator Delta) *
        cayleyDenominator (diracOperator Delta) =
      !![1 - Delta * star Delta, 0;
         0, 1 - star Delta * Delta] := by
  calc
    cayleyNumerator (diracOperator Delta) *
          cayleyDenominator (diracOperator Delta) =
        1 - diracSquare Delta := by
          rw [cayley_product_eq_one_sub_square]
          rfl
    _ = !![1 - Delta * star Delta, 0;
           0, 1 - star Delta * Delta] := by
      rw [diracSquare_eq_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

def gradingShift : BdGBlock A :=
  1 + chiralGrading

@[simp] theorem gradingShift_sq :
    (gradingShift (A := A)) * gradingShift =
      (2 : A) • (gradingShift (A := A)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
      simp [gradingShift, chiralGrading, Matrix.mul_apply, Matrix.vecMul,
      Fin.sum_univ_two, Matrix.vecHead, Matrix.vecCons] <;> noncomm_ring

theorem gradingShift_dirac_identity (Delta : A) :
    gradingShift * diracOperator Delta +
        diracOperator Delta * gradingShift =
      (2 : A) • diracOperator Delta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gradingShift, diracOperator, chiralGrading,
      Matrix.mul_apply, Matrix.vecMul, Fin.sum_univ_two,
      Matrix.vecHead, Matrix.vecCons] <;> noncomm_ring

end InfoGeometry.Physics.NCG

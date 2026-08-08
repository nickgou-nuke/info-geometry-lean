import InfoGeometry.Physics.BdGChiralBlockMatrix
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Physics.Geometry

namespace LegacyCayleyPoincareTransform

open InfoGeometry.Physics

variable {A : Type*} [CommRing A] [StarRing A]

/-- The numerator and denominator polynomials of the Cayley transform.
No inverse is assumed here. -/
def cayleyNumerator (D : BdGBlock A) : BdGBlock A := 1 - D

def cayleyDenominator (D : BdGBlock A) : BdGBlock A := 1 + D

@[simp] theorem cayley_dirac_product (Delta : A) :
    cayleyNumerator (diracOperator Delta) *
        cayleyDenominator (diracOperator Delta) =
      !![1 - Delta * star Delta, 0;
         0, 1 - star Delta * Delta] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cayleyNumerator, cayleyDenominator, diracOperator,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def artinBraidGenerator : BdGBlock A := 1 + chiralGrading

@[simp] theorem artin_generator_sq :
    artinBraidGenerator (A := A) * artinBraidGenerator (A := A) =
      2 • artinBraidGenerator (A := A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [artinBraidGenerator, chiralGrading, Matrix.mul_apply,
      Matrix.add_apply, Matrix.one_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] <;> ring

theorem braid_dirac_identity (Delta : A) :
    artinBraidGenerator (A := A) * diracOperator Delta +
        diracOperator Delta * artinBraidGenerator (A := A) =
      2 • diracOperator Delta := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [artinBraidGenerator, diracOperator, chiralGrading,
      Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two] <;> ring

end LegacyCayleyPoincareTransform

end InfoGeometry.Physics.Geometry

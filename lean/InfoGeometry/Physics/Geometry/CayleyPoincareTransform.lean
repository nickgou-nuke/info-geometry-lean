import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Physics.Geometry

open InfoGeometry.Physics

variable {A : Type*} [Ring A] [StarRing A]

/-- The numerator and denominator polynomials of the Cayley expression
`(1 - D) (1 + D)⁻¹`.  No inverse is assumed here. -/
def cayleyNumerator (D : BdGBlock A) : BdGBlock A := 1 - D

def cayleyDenominator (D : BdGBlock A) : BdGBlock A := 1 + D

@[simp] theorem cayley_generates_diagonal_metric (Delta : A) :
    cayleyNumerator (diracOperator Delta) *
        cayleyDenominator (diracOperator Delta) =
      !![1 - Delta * star Delta, 0;
         0, 1 - star Delta * Delta] := by
  rw [cayleyNumerator, cayleyDenominator]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracOperator, Matrix.mul_apply, Fin.sum_univ_two] <;>
    noncomm_ring

def artinBraidGenerator : BdGBlock A := 1 + chiralGrading

@[simp] theorem artin_braid_projector :
    artinBraidGenerator (A := A) * artinBraidGenerator (A := A) =
      (2 : ℕ) • artinBraidGenerator (A := A) := by
  rw [artinBraidGenerator]
  calc
    ((1 : BdGBlock A) + chiralGrading) *
        ((1 : BdGBlock A) + chiralGrading) =
        (1 : BdGBlock A) + chiralGrading + chiralGrading +
          chiralGrading * chiralGrading := by noncomm_ring
    _ = (2 : ℕ) • ((1 : BdGBlock A) + chiralGrading) := by
      rw [chiralGrading_sq]
      module

theorem braid_dirac_entanglement (Delta : A) :
    artinBraidGenerator (A := A) * diracOperator Delta +
        diracOperator Delta * artinBraidGenerator (A := A) =
      (2 : ℕ) • diracOperator Delta := by
  rw [artinBraidGenerator]
  calc
    ((1 : BdGBlock A) + chiralGrading) * diracOperator Delta +
        diracOperator Delta * ((1 : BdGBlock A) + chiralGrading) =
      2 • diracOperator Delta +
        (chiralGrading * diracOperator Delta +
          diracOperator Delta * chiralGrading) := by noncomm_ring
    _ = 2 • diracOperator Delta := by
      rw [add_comm (chiralGrading * diracOperator Delta)
        (diracOperator Delta * chiralGrading),
        dirac_anticommutes_with_chirality]
      simp

end InfoGeometry.Physics.Geometry

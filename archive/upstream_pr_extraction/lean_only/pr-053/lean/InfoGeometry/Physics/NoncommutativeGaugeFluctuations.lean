import InfoGeometry.Physics.ConnesDifferentialInnerFluctuations

namespace InfoGeometry.Physics

variable {A : Type*} [Ring A] [StarRing A]

/-- A single finite-matrix inner fluctuation term `a [D,b]`. -/
def innerFluctuationTerm
    (Delta alpha beta gamma delta : A) : BdGBlock A :=
  diagonalObservable alpha beta *
    connesDifferential (diracOperator Delta) (diagonalObservable gamma delta)

@[simp] theorem innerFluctuationTerm_eq
    (Delta alpha beta gamma delta : A) :
    innerFluctuationTerm Delta alpha beta gamma delta =
      !![0, alpha * (Delta * delta - gamma * Delta);
         beta * (star Delta * gamma - delta * star Delta), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [innerFluctuationTerm, diagonalObservable, connesDifferential,
      diracOperator, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem innerFluctuationTerm_isOffDiagonal
    (Delta alpha beta gamma delta : A) :
    BdGIsOffDiagonal (innerFluctuationTerm Delta alpha beta gamma delta) := by
  rw [innerFluctuationTerm_eq]
  exact ⟨rfl, rfl⟩

/-- An arbitrary off-diagonal gauge-field carrier. -/
def offDiagonalGaugeField (upper lower : A) : BdGBlock A :=
  !![0, upper; lower, 0]

@[simp] theorem offDiagonalGaugeField_isOffDiagonal
    (upper lower : A) :
    BdGIsOffDiagonal (offDiagonalGaugeField upper lower) := by
  exact ⟨rfl, rfl⟩

/-- The finite perturbed Dirac operator `D + A`. -/
def perturbedDirac (Delta upper lower : A) : BdGBlock A :=
  diracOperator Delta + offDiagonalGaugeField upper lower

theorem perturbedDirac_anticommutes_chiral
    (Delta upper lower : A) :
    perturbedDirac Delta upper lower * chiralGrading +
        chiralGrading * perturbedDirac Delta upper lower =
      (0 : BdGBlock A) := by
  apply innerFluctuatedDirac_anticommutes_chiral
  · exact diracOperator_isOffDiagonal Delta
  · exact offDiagonalGaugeField_isOffDiagonal upper lower

end InfoGeometry.Physics

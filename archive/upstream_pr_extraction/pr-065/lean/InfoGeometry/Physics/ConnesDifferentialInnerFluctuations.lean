import InfoGeometry.Physics.ConnesQuantumDifferential

namespace InfoGeometry.Physics

variable {A : Type*} [Ring A] [StarRing A]

def BdGIsDiagonal (M : BdGBlock A) : Prop :=
  M 0 1 = 0 ∧ M 1 0 = 0

def BdGIsOffDiagonal (M : BdGBlock A) : Prop :=
  M 0 0 = 0 ∧ M 1 1 = 0

@[simp] theorem diracOperator_isOffDiagonal (Delta : A) :
    BdGIsOffDiagonal (diracOperator Delta) := by
  exact ⟨rfl, rfl⟩

theorem connesDifferential_diagonal_isOffDiagonal
    (D a : BdGBlock A)
    (hD : BdGIsOffDiagonal D)
    (ha : BdGIsDiagonal a) :
    BdGIsOffDiagonal (connesDifferential D a) := by
  rcases hD with ⟨hD00, hD11⟩
  rcases ha with ⟨ha01, ha10⟩
  constructor
  · simp [BdGIsOffDiagonal, connesDifferential, Matrix.mul_apply,
      Fin.sum_univ_two, hD00, ha10, ha01]
  · simp [BdGIsOffDiagonal, connesDifferential, Matrix.mul_apply,
      Fin.sum_univ_two, hD00, hD11, ha01, ha10]

theorem offDiagonal_anticommutes_chiral
    (M : BdGBlock A) (hM : BdGIsOffDiagonal M) :
    M * chiralGrading + chiralGrading * M = (0 : BdGBlock A) := by
  rcases hM with ⟨hM00, hM11⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralGrading, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two, hM00, hM11]

def innerFluctuatedDirac (D A₁ : BdGBlock A) : BdGBlock A := D + A₁

theorem innerFluctuatedDirac_anticommutes_chiral
    (D A₁ : BdGBlock A)
    (hD : BdGIsOffDiagonal D)
    (hA : BdGIsOffDiagonal A₁) :
    innerFluctuatedDirac D A₁ * chiralGrading +
        chiralGrading * innerFluctuatedDirac D A₁ =
      (0 : BdGBlock A) := by
  apply offDiagonal_anticommutes_chiral
  rcases hD with ⟨hD00, hD11⟩
  rcases hA with ⟨hA00, hA11⟩
  constructor <;> simp [innerFluctuatedDirac, hD00, hD11, hA00, hA11]

/-!
The basic Dirac operator and the commutator with a diagonal observable form
an explicit inner fluctuation.  This is the concrete finite-matrix synthesis
of the two closure lemmas above.
-/
theorem dirac_plus_diagonal_commutator_anticommutes_chiral
    (Delta : A) (a : BdGBlock A) (ha : BdGIsDiagonal a) :
    innerFluctuatedDirac (diracOperator Delta)
        (connesDifferential (diracOperator Delta) a) * chiralGrading +
        chiralGrading * innerFluctuatedDirac (diracOperator Delta)
          (connesDifferential (diracOperator Delta) a) =
      (0 : BdGBlock A) := by
  apply innerFluctuatedDirac_anticommutes_chiral
  · exact diracOperator_isOffDiagonal Delta
  · exact connesDifferential_diagonal_isOffDiagonal
      (diracOperator Delta) a (diracOperator_isOffDiagonal Delta) ha

end InfoGeometry.Physics

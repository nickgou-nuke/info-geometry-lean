import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzMatrixUnits
import InfoGeometry.Algebra.CuntzSuperalgebra

/-!
# Five-grade weights on the finite Cuntz matrix-unit sector

For `E i j = S i S j†`, the native matrix-unit law gives
`E i j * E k l = δ(j,k) E i l`.  The grading below is only the finite
matrix-unit sector of `CuntzAlg 3`; it is not a decomposition theorem for the
whole Cuntz algebra and it is not a TKK property.
-/

noncomputable section

namespace InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzMatrixUnits
open InfoGeometry.Algebra.CuntzSuperalgebra

abbrev Cuntz3 := CuntzAlg 3

def hop (i j : Fin 3) : Cuntz3 := E 3 i j

def commutator (x y : Cuntz3) : Cuntz3 := x * y - y * x

def colourWeight (i : Fin 3) : ℤ :=
  if i = 0 then 1 else if i = 1 then -1 else 0

def gradingOp : Cuntz3 := hop 0 0 - hop 1 1

def IsGradedComponent (h : Cuntz3) (k : ℂ) (x : Cuntz3) : Prop :=
  commutator h x = k • x

theorem hop_mul_hop (i j k l : Fin 3) :
    hop i j * hop k l = if j = k then hop i l else 0 := by
  exact matrix_unit_mul 3 i j k l

/-- The matrix-unit hopping sector is even for the native Cuntz parity. -/
theorem parity_hop (i j : Fin 3) :
    parity 3 (hop i j) = hop i j := by
  calc
    parity 3 (hop i j) =
        parity 3 (cuntzS 3 i) * parity 3 (cuntzSdag 3 j) := by
      rw [hop, E, map_mul]
    _ = (-cuntzS 3 i) * (-cuntzSdag 3 j) := by
      rw [parity_S, parity_Sdag]
    _ = hop i j := by
      change
        (- (cuntzS 3 i) : CuntzAlg 3) *
            (- (cuntzSdag 3 j) : CuntzAlg 3) =
          cuntzS 3 i * cuntzSdag 3 j
      exact neg_mul_neg (cuntzS 3 i) (cuntzSdag 3 j)

/-- The Cartan grading operator belongs to the even Cuntz sector. -/
theorem parity_gradingOp :
    parity 3 gradingOp = gradingOp := by
  rw [gradingOp, map_sub, parity_hop, parity_hop]

theorem gradingOp_comm_hop (i j : Fin 3) :
    commutator (gradingOp) (hop i j) =
      ((colourWeight i - colourWeight j : ℤ) : ℂ) • hop i j := by
  fin_cases i <;> fin_cases j <;>
    simp [commutator, gradingOp, hop, colourWeight,
      sub_mul, mul_sub, matrix_unit_mul, one_smul, two_smul] <;>
    module

theorem hop_zero_one_mem_grade_two :
    IsGradedComponent gradingOp 2 (hop 0 1) := by
  unfold IsGradedComponent
  simpa [colourWeight] using gradingOp_comm_hop 0 1

theorem hop_one_zero_mem_grade_neg_two :
    IsGradedComponent gradingOp (-2) (hop 1 0) := by
  unfold IsGradedComponent
  simpa [colourWeight] using gradingOp_comm_hop 1 0

theorem hop_zero_two_mem_grade_one :
    IsGradedComponent gradingOp 1 (hop 0 2) := by
  change commutator gradingOp (hop 0 2) = (1 : ℂ) • hop 0 2
  simpa [colourWeight] using gradingOp_comm_hop 0 2

theorem hop_two_zero_mem_grade_neg_one :
    IsGradedComponent gradingOp (-1) (hop 2 0) := by
  unfold IsGradedComponent
  simpa [colourWeight] using gradingOp_comm_hop 2 0

theorem hop_two_two_mem_grade_zero :
    IsGradedComponent gradingOp 0 (hop 2 2) := by
  change commutator gradingOp (hop 2 2) = (0 : ℂ) • hop 2 2
  simpa [colourWeight] using gradingOp_comm_hop 2 2

theorem gradingOp_sq :
    gradingOp * gradingOp = hop 0 0 + hop 1 1 := by
  simp [gradingOp, hop, sub_mul, mul_sub, matrix_unit_mul]

theorem gradingOp_cube :
    gradingOp * gradingOp * gradingOp = gradingOp := by
  calc
    gradingOp * gradingOp * gradingOp =
        (gradingOp * gradingOp) * gradingOp := rfl
    _ = (hop 0 0 + hop 1 1) * gradingOp := by rw [gradingOp_sq]
    _ = gradingOp := by
      simp [gradingOp, hop, add_mul, mul_sub, matrix_unit_mul]

end InfoGeometry.Algebra.CuntzMatrixUnitFiveGradingBridge

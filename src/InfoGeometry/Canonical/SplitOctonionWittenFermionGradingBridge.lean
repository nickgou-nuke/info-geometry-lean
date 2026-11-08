import InfoGeometry.Lie.SplitOctonionWittHypercomplexPlaneBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.FiniteParitySupertrace

/-!
# Concrete split-octonion grading and finite Witten parity readout

This owner records the finite-dimensional part of the Witten/Möbius
dictionary.  The middle-sign operator is a genuine parity involution on the
8-dimensional Witt coordinate carrier.  Its finite supertrace is an operator
readout; it is not identified with the arithmetic Möbius function.  Möbius
parity remains a separate square-free coefficient theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionWittenFermionGradingBridge

open InfoGeometry.Lie.SplitOctonionWittHypercomplexPlaneBridge
open InfoGeometry.OperatorAlgebra.FiniteParitySupertrace
open Matrix

abbrev Mat8 := InfoGeometry.Lie.SplitOctonionWittHypercomplexPlaneBridge.Mat8

/-- The geometric parity signs on the ordered Witt carrier. -/
def wittParitySign : Fin 8 → ℝ :=
  ![1, -1, -1, -1, 1, -1, -1, -1]

/-- Diagonal parity operator associated with the longitudinal/transverse sign. -/
def wittParityOperator : Mat8 := Matrix.diagonal wittParitySign

theorem wittParityOperator_eq_middleSign :
    wittParityOperator = longitudinalTransverseMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wittParityOperator, wittParitySign,
      longitudinalTransverseMat]

theorem wittParitySign_sq (i : Fin 8) :
    wittParitySign i ^ 2 = 1 := by
  fin_cases i <;> norm_num [wittParitySign]

theorem wittParityOperator_sq :
    wittParityOperator * wittParityOperator = (1 : Mat8) := by
  rw [wittParityOperator_eq_middleSign]
  exact longitudinalTransverseMat_sq

def wittPositiveProjector : Mat8 :=
  positiveParityProjector wittParitySign

def wittNegativeProjector : Mat8 :=
  negativeParityProjector wittParitySign

theorem wittProjector_packet :
    wittPositiveProjector * wittPositiveProjector = wittPositiveProjector ∧
      wittNegativeProjector * wittNegativeProjector = wittNegativeProjector ∧
      wittPositiveProjector * wittNegativeProjector = 0 ∧
      wittNegativeProjector * wittPositiveProjector = 0 ∧
      wittPositiveProjector + wittNegativeProjector = (1 : Mat8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact positiveParityProjector_idempotent wittParitySign wittParitySign_sq
  · exact negativeParityProjector_idempotent wittParitySign wittParitySign_sq
  · exact parityProjectors_orthogonal wittParitySign wittParitySign_sq
  · ext i j
    by_cases h : i = j
    · subst j
      fin_cases i <;>
        norm_num [wittPositiveProjector, wittNegativeProjector,
          positiveParityProjector, negativeParityProjector,
          wittParitySign, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_succ]
    · simp [wittPositiveProjector, wittNegativeProjector,
        positiveParityProjector, negativeParityProjector, h]
  · simpa [wittPositiveProjector, wittNegativeProjector] using
      positiveParityProjector_add_negativeParityProjector wittParitySign

def wittSupertrace (A : Mat8) : ℝ :=
  supertrace wittParitySign A

theorem wittSupertrace_eq_signed_diagonal (A : Mat8) :
    wittSupertrace A = ∑ i, wittParitySign i * A i i := by
  exact supertrace_eq_sum_sign_mul_diagonal wittParitySign A

theorem wittParitySupertrace :
    wittSupertrace (1 : Mat8) = -4 := by
  rw [wittSupertrace_eq_signed_diagonal]
  norm_num [wittParitySign, Matrix.one_apply, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]

end InfoGeometry.Canonical.SplitOctonionWittenFermionGradingBridge

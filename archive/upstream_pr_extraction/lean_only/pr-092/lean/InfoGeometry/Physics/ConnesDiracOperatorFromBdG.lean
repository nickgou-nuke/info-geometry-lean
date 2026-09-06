import InfoGeometry.Physics.OperatorZornNambuGorkovBridge

namespace InfoGeometry.Physics.NCG

open InfoGeometry.Physics
open OperatorZornMatrix

variable {A : Type*} [Ring A] [StarRing A]

/-- Diagonal grading packet.  This is an operator-valued grading datum; it is
not by itself a represented Hilbert-space grading. -/
def chiralGradingOperator : OperatorZornMatrix A where
  n_plus_op := 1
  n_minus_op := -1
  sigma_plus_op := 0
  sigma_minus_op := 0

/-- Purely off-diagonal Dirac/BdG packet with gap entry `Delta`. -/
def diracOperator (Delta : A) : OperatorZornMatrix A where
  n_plus_op := 0
  n_minus_op := 0
  sigma_plus_op := Delta
  sigma_minus_op := star Delta

def addZorn (M N : OperatorZornMatrix A) : OperatorZornMatrix A where
  n_plus_op := M.n_plus_op + N.n_plus_op
  n_minus_op := M.n_minus_op + N.n_minus_op
  sigma_plus_op := M.sigma_plus_op + N.sigma_plus_op
  sigma_minus_op := M.sigma_minus_op + N.sigma_minus_op

def diracMulGrading (Delta : A) : OperatorZornMatrix A where
  n_plus_op := 0
  n_minus_op := 0
  sigma_plus_op := -Delta
  sigma_minus_op := star Delta

def gradingMulDirac (Delta : A) : OperatorZornMatrix A where
  n_plus_op := 0
  n_minus_op := 0
  sigma_plus_op := Delta
  sigma_minus_op := -star Delta

theorem dirac_anticommutes_with_chirality (Delta : A) :
    addZorn (diracMulGrading Delta) (gradingMulDirac Delta) =
      ({ n_plus_op := 0, n_minus_op := 0,
         sigma_plus_op := 0, sigma_minus_op := 0 } : OperatorZornMatrix A) := by
  simp [addZorn, diracMulGrading, gradingMulDirac]

end InfoGeometry.Physics.NCG

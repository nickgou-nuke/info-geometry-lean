import InfoGeometry.Canonical.BiquaternionNegativeRootsLog

/-!
# Biquaternion logarithm monodromy

Integrated repair of the external logarithm/monodromy file.  The useful content
is the Pauli-vector square-root algebra and integer logarithm branch shifts;
these are routed through `BiquaternionNegativeRootsLog`.
-/

noncomputable section

namespace BiquaternionLogarithmMonodromy

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

def σ₁ : M2C := BiquaternionNegativeRootsLog.σ₁
def σ₂ : M2C := BiquaternionNegativeRootsLog.σ₂
def σ₃ : M2C := BiquaternionNegativeRootsLog.σ₃

def tracelessPauli (x y z : ℂ) : M2C := BiquaternionNegativeRootsLog.T x y z

theorem tracelessPauli_sq (x y z : ℂ) :
    tracelessPauli x y z * tracelessPauli x y z =
      (x * x + y * y + z * z) • (1 : M2C) := by
  have imported_square := BiquaternionNegativeRootsLog.T_sq x y z
  simpa [tracelessPauli] using imported_square

theorem tracelessPauli_sq_neg_one (x y z : ℂ) (h : x * x + y * y + z * z = -1) :
    tracelessPauli x y z * tracelessPauli x y z = -(1 : M2C) := by
  have imported_square_root :=
    BiquaternionNegativeRootsLog.traceless_square_root_neg_one x y z h
  simpa [tracelessPauli] using imported_square_root

/-- Logarithm branch shift by `2πin`. -/
def logBranchShift (n : ℤ) : ℂ := BiquaternionNegativeRootsLog.logBranchShift n

theorem logBranchShift_add (m n : ℤ) :
    logBranchShift (m + n) = logBranchShift m + logBranchShift n := by
  have imported_add := BiquaternionNegativeRootsLog.logBranchShift_add m n
  simpa [logBranchShift] using imported_add

theorem iσ₂_square_root_neg_one : (Complex.I • σ₂) * (Complex.I • σ₂) = -(1 : M2C) := by
  have imported_square_root := BiquaternionNegativeRootsLog.iσ₂_square_root_neg_one
  simpa [σ₂] using imported_square_root

#check tracelessPauli_sq
#check tracelessPauli_sq_neg_one
#check logBranchShift_add
#check iσ₂_square_root_neg_one

end BiquaternionLogarithmMonodromy

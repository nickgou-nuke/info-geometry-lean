import InfoGeometry.Canonical.BiquaternionNegativeRootsLog
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Biquaternion logarithm monodromy

Maintained owner for the recovered logarithm/monodromy finite slice. The useful
content is the Pauli-vector square-root algebra together with additive integer
logarithm-branch shifts, routed through the canonical negative-roots owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.BiquaternionLogarithmMonodromy

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

def σ₁ : M2C := BiquaternionNegativeRootsLog.σ₁
def σ₂ : M2C := BiquaternionNegativeRootsLog.σ₂
def σ₃ : M2C := BiquaternionNegativeRootsLog.σ₃

def tracelessPauli (x y z : ℂ) : M2C := BiquaternionNegativeRootsLog.T x y z

theorem tracelessPauli_sq (x y z : ℂ) :
    tracelessPauli x y z * tracelessPauli x y z =
      (x * x + y * y + z * z) • (1 : M2C) :=
  BiquaternionNegativeRootsLog.T_sq x y z

theorem tracelessPauli_sq_neg_one (x y z : ℂ) (h : x * x + y * y + z * z = -1) :
    tracelessPauli x y z * tracelessPauli x y z = -(1 : M2C) :=
  BiquaternionNegativeRootsLog.traceless_square_root_neg_one x y z h

/-- Logarithm branch shift by `2πin`. -/
def logBranchShift (n : ℤ) : ℂ := BiquaternionNegativeRootsLog.logBranchShift n

theorem logBranchShift_add (m n : ℤ) :
    logBranchShift (m + n) = logBranchShift m + logBranchShift n :=
  BiquaternionNegativeRootsLog.logBranchShift_add m n

/-- Consolidated monodromy socket: square roots of `-I` plus additive branch shifts. -/
theorem logarithm_monodromy_synthesis :
    ((Complex.I • σ₂) * (Complex.I • σ₂) = -(1 : M2C)) ∧
    (∀ m n : ℤ, logBranchShift (m + n) = logBranchShift m + logBranchShift n) := by
  exact ⟨BiquaternionNegativeRootsLog.iσ₂_square_root_neg_one, logBranchShift_add⟩

end InfoGeometry.Canonical.BiquaternionLogarithmMonodromy

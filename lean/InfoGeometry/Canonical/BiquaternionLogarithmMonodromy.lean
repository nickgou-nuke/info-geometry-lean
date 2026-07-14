import InfoGeometry.Canonical.BiquaternionNegativeRootsLog

/-!
# Biquaternion logarithm monodromy

Maintained owner for the recovered logarithm/monodromy finite slice. The useful
content is the Pauli-vector square-root algebra together with additive integer
logarithm-branch shifts, routed through the canonical negative-roots owner.
-/

noncomputable section

namespace BiquaternionLogarithmMonodromy

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

def σ₁ : M2C := InfoGeometry.Canonical.BiquaternionNegativeRootsLog.σ₁
def σ₂ : M2C := InfoGeometry.Canonical.BiquaternionNegativeRootsLog.σ₂
def σ₃ : M2C := InfoGeometry.Canonical.BiquaternionNegativeRootsLog.σ₃

def tracelessPauli (x y z : ℂ) : M2C := InfoGeometry.Canonical.BiquaternionNegativeRootsLog.T x y z

theorem tracelessPauli_sq (x y z : ℂ) :
    tracelessPauli x y z * tracelessPauli x y z =
      (x * x + y * y + z * z) • (1 : M2C) :=
  InfoGeometry.Canonical.BiquaternionNegativeRootsLog.T_sq x y z

theorem tracelessPauli_sq_neg_one (x y z : ℂ) (h : x * x + y * y + z * z = -1) :
    tracelessPauli x y z * tracelessPauli x y z = -(1 : M2C) :=
  InfoGeometry.Canonical.BiquaternionNegativeRootsLog.traceless_square_root_neg_one x y z h

/-- Logarithm branch shift by `2πin`. -/
def logBranchShift (n : ℤ) : ℂ := InfoGeometry.Canonical.BiquaternionNegativeRootsLog.logBranchShift n

theorem logBranchShift_add (m n : ℤ) :
    logBranchShift (m + n) = logBranchShift m + logBranchShift n :=
  InfoGeometry.Canonical.BiquaternionNegativeRootsLog.logBranchShift_add m n

/-- Consolidated monodromy socket: square roots of `-I` plus additive branch shifts. -/
theorem logarithm_monodromy_synthesis :
    ((Complex.I • σ₂) * (Complex.I • σ₂) = -(1 : M2C)) ∧
    (∀ m n : ℤ, logBranchShift (m + n) = logBranchShift m + logBranchShift n) := by
  exact ⟨InfoGeometry.Canonical.BiquaternionNegativeRootsLog.iσ₂_square_root_neg_one, logBranchShift_add⟩

end BiquaternionLogarithmMonodromy

import InfoGeometry.Physics.FiniteRelativeModularOperator
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

/-!
# Finite relative modular logarithms

The logarithmic bridge is kept at the diagonal eigenvalue level.  No generic
matrix logarithm or Tomita standard-form theorem is introduced here.
-/

namespace InfoGeometry.Physics.FiniteRelativeModularLogBridge

def relativeLogEigenvalue (p q : ℝ) : ℝ :=
  -Real.log p + Real.log q

theorem relativeLogEigenvalue_eq_neg_log_ratio
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    relativeLogEigenvalue p q = -Real.log (p / q) := by
  unfold relativeLogEigenvalue
  rw [Real.log_div hp.ne' hq.ne']
  ring

theorem relativeLogEigenvalue_inverse
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    relativeLogEigenvalue q p = -relativeLogEigenvalue p q := by
  unfold relativeLogEigenvalue
  ring

theorem relativeLogAction_unit
    {p q c : ℝ} :
    relativeLogEigenvalue p q * c =
      (-Real.log p + Real.log q) * c := by
  rfl

theorem leftRightSurprisal_unit
    {p q c : ℝ} :
    (-Real.log p) * c - (-Real.log q) * c =
      relativeLogEigenvalue p q * c := by
  unfold relativeLogEigenvalue
  ring

theorem relativeLog_eq_leftRightSurprisal
    {p q : ℝ} :
    relativeLogEigenvalue p q = (-Real.log p) - (-Real.log q) := by
  unfold relativeLogEigenvalue
  ring

end InfoGeometry.Physics.FiniteRelativeModularLogBridge

import Mathlib
import InfoGeometry.Canonical.SplitQuaternionConcrete

noncomputable section

namespace InfoGeometry.Clifford

def splitQuaternionGradeInvolution (q : SplitQuaternion) : SplitQuaternion :=
  ⟨q.w, -q.x, -q.y, q.z⟩

def splitQuaternionReversion (q : SplitQuaternion) : SplitQuaternion :=
  ⟨q.w, q.x, q.y, -q.z⟩

def splitQuaternionCliffordConjugation (q : SplitQuaternion) : SplitQuaternion :=
  splitQuaternionGradeInvolution (splitQuaternionReversion q)

theorem splitQuaternion_conjugation_eq_clifford_conjugation (q : SplitQuaternion) :
    conjugate q = splitQuaternionCliffordConjugation q := by
  ext <;> dsimp [conjugate, splitQuaternionCliffordConjugation,
                 splitQuaternionGradeInvolution, splitQuaternionReversion]

/-- The Clifford conjugation is an anti-automorphism. -/
theorem splitQuaternion_conjugate_mul (q1 q2 : SplitQuaternion) :
    conjugate (q1 * q2) = conjugate q2 * conjugate q1 := by
  ext <;> simp [conjugate, mul_def] <;> ring

/-- The quadratic norm induced by the Clifford conjugation has signature (2,2). -/
theorem splitQuaternion_norm_signature (q : SplitQuaternion) :
    norm q = q.w ^ 2 + q.x ^ 2 - q.y ^ 2 - q.z ^ 2 := by
  change q.w * q.w + q.x * q.x - q.y * q.y - q.z * q.z = _
  ring

end InfoGeometry.Clifford

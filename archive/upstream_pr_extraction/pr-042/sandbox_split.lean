import InfoGeometry.Projective.Cl44QuaternionSplit

namespace InfoGeometry.Projective
open Matrix

lemma test_mul (X Y : SplitOctonion) :
  (splitOctonionToMatrix X * splitOctonionToMatrix Y) 0 0 = X.q1 * Y.q1 + X.q2 * star Y.q2 := by
  dsimp [splitOctonionToMatrix]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

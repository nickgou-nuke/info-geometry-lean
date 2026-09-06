import InfoGeometry.Projective.Cl44QuaternionSplit

namespace InfoGeometry.Projective

open Matrix

lemma split_octonion_is_associative (X Y Z : SplitOctonion) :
    splitOctonionMul (splitOctonionMul X Y) Z = splitOctonionMul X (splitOctonionMul Y Z) := by
  dsimp [splitOctonionMul]
  ext
  · simp
    sorry -- Let's just check if it's provable by ring/simp, though quaternions are noncommutative.
  · simp
    sorry
end InfoGeometry.Projective

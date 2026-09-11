import InfoGeometry.Algebra.SplitCayleyF2
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Algebra.SplitCayleyF2

theorem delta1_norm_structural (r : Vec3) (x : Cayley) :
    norm (delta1 r x) = norm x := by
  cases x with
  | mk xa xu xv xb =>
    simp [norm, delta1, dot, cross]
    ring

theorem delta2_norm_structural (r : Vec3) (x : Cayley) :
    norm (delta2 r x) = norm x := by
  cases x with
  | mk xa xu xv xb =>
    have htwo : (2 : Scalar) = 0 := CharP.cast_eq_zero Scalar 2
    simp [norm, delta2, dot, cross]
    ring_nf
    simp [htwo]

end InfoGeometry.Algebra.SplitCayleyF2

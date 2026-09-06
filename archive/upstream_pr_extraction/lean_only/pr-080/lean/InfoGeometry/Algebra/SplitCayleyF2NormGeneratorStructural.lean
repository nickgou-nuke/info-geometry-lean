import InfoGeometry.Algebra.SplitCayleyF2NormStructural

namespace InfoGeometry.Algebra.SplitCayleyF2

theorem cyclicAction_norm_structural (x : Cayley) :
    norm (cyclicAction x) = norm x := by
  cases x with
  | mk xa xu xv xb =>
    simp [norm, cyclicAction, cyclic, dot]
    ring

theorem shearAction_norm_structural (x : Cayley) :
    norm (shearAction x) = norm x := by
  cases x with
  | mk xa xu xv xb =>
    simp [norm, shearAction, shearU, shearV, dot]
    have htwo : (2 : Scalar) = 0 := CharP.cast_eq_zero Scalar 2
    calc
      (xu 0 + xu 1) * xv 0 + xu 1 * (xv 1 + xv 0) =
          (xu 0 * xv 0 + xu 1 * xv 1) +
            (2 : Scalar) * (xu 1 * xv 0) := by ring
      _ = xu 0 * xv 0 + xu 1 * xv 1 := by
        simp [htwo]

end InfoGeometry.Algebra.SplitCayleyF2

import InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

theorem test (L : Fin 3 → ℝ) (i : Fin 8) :
    circularPeirceBasis.equivFun (circularPeirceBasis i) = fun j => if i = j then 1 else 0 := by
  ext j
  change circularPeirceBasis.repr (circularPeirceBasis i) j = _
  exact circularPeirceBasis.repr_self_apply i j

import InfoGeometry.Lie.SplitOctonionCircularCartanScaling

open InfoGeometry.Lie.SplitOctonionCircularCartanScaling
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

theorem test (L : Fin 3 → ℝ) (i : Fin 8) :
    circularCartanScaling L (circularPeirceBasis i) =
      circularCartanScalingDiag L i • circularPeirceBasis i := by
  have H1 : circularPeirceBasis.equivFun (circularPeirceBasis i) = fun j => if i = j then 1 else 0 := by
    ext j
    change circularPeirceBasis.repr (circularPeirceBasis i) j = _
    exact circularPeirceBasis.repr_self_apply i j
  unfold circularCartanScaling
  change circularPeirceBasis.equivFun.symm (circularCartanScalingCoord L (circularPeirceBasis.equivFun (circularPeirceBasis i))) = _
  rw [H1]
  have H2 : circularCartanScalingCoord L (fun j => if i = j then 1 else 0) = fun j => if i = j then circularCartanScalingDiag L i else 0 := by
    ext j
    simp [circularCartanScalingCoord]
    split_ifs with h
    · subst h; ring
    · ring
  rw [H2]
  have H3 : (fun j => if i = j then circularCartanScalingDiag L i else 0) =
      circularCartanScalingDiag L i • (fun j => if i = j then (1:ℝ) else 0) := by
    ext j
    simp
  rw [H3, ← H1]
  rw [LinearEquiv.map_smul, LinearEquiv.symm_apply_apply]


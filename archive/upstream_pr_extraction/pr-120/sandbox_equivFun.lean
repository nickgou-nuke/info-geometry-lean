import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

theorem equivFun_basis (j : Fin 8) :
    circularPeirceBasis.equivFun (circularPeirceBasis j) = Pi.single j 1 := by
  simp only [Basis.equivFun_apply, Basis.repr_self, Finsupp.single_eq_pi_single,
    Finsupp.equivFunOnFintype_single]

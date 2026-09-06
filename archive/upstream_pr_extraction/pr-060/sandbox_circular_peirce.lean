import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

namespace InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

theorem circularPeirceBasis_explicit_expansion (X : CanonicalZorn) :
    X = circularCoordinate (cartesianZornLinearEquiv.symm X) 0 • cartesianZornLinearEquiv scalarPlus
      + (∑ i : Fin 3, circularCoordinate (cartesianZornLinearEquiv.symm X) ⟨i.val + 1, by omega⟩ • cartesianZornLinearEquiv (rootPlus i))
      + circularCoordinate (cartesianZornLinearEquiv.symm X) 4 • cartesianZornLinearEquiv scalarMinus
      + (∑ i : Fin 3, circularCoordinate (cartesianZornLinearEquiv.symm X) ⟨i.val + 5, by omega⟩ • cartesianZornLinearEquiv (rootMinus i)) := by
  have h := circularPeirceBasis_reconstruct X
  rw [Fin.sum_univ_eight] at h
  have h1 : ∑ i : Fin 3, circularCoordinate (cartesianZornLinearEquiv.symm X) ⟨i.val + 1, by omega⟩ • cartesianZornLinearEquiv (rootPlus i) =
    circularCoordinate (cartesianZornLinearEquiv.symm X) 1 • cartesianZornLinearEquiv (rootPlus 0)
      + circularCoordinate (cartesianZornLinearEquiv.symm X) 2 • cartesianZornLinearEquiv (rootPlus 1)
      + circularCoordinate (cartesianZornLinearEquiv.symm X) 3 • cartesianZornLinearEquiv (rootPlus 2) := by
    rw [Fin.sum_univ_three]
    rfl
  have h2 : ∑ i : Fin 3, circularCoordinate (cartesianZornLinearEquiv.symm X) ⟨i.val + 5, by omega⟩ • cartesianZornLinearEquiv (rootMinus i) =
    circularCoordinate (cartesianZornLinearEquiv.symm X) 5 • cartesianZornLinearEquiv (rootMinus 0)
      + circularCoordinate (cartesianZornLinearEquiv.symm X) 6 • cartesianZornLinearEquiv (rootMinus 1)
      + circularCoordinate (cartesianZornLinearEquiv.symm X) 7 • cartesianZornLinearEquiv (rootMinus 2) := by
    rw [Fin.sum_univ_three]
    rfl
  rw [h1, h2]
  have h0 : circularPeirceBasis 0 = cartesianZornLinearEquiv scalarPlus := circularPeirceBasis_apply 0
  have h1' : circularPeirceBasis 1 = cartesianZornLinearEquiv (rootPlus 0) := circularPeirceBasis_apply 1
  have h2' : circularPeirceBasis 2 = cartesianZornLinearEquiv (rootPlus 1) := circularPeirceBasis_apply 2
  have h3' : circularPeirceBasis 3 = cartesianZornLinearEquiv (rootPlus 2) := circularPeirceBasis_apply 3
  have h4' : circularPeirceBasis 4 = cartesianZornLinearEquiv scalarMinus := circularPeirceBasis_apply 4
  have h5' : circularPeirceBasis 5 = cartesianZornLinearEquiv (rootMinus 0) := circularPeirceBasis_apply 5
  have h6' : circularPeirceBasis 6 = cartesianZornLinearEquiv (rootMinus 1) := circularPeirceBasis_apply 6
  have h7' : circularPeirceBasis 7 = cartesianZornLinearEquiv (rootMinus 2) := circularPeirceBasis_apply 7
  rw [h0, h1', h2', h3', h4', h5', h6', h7'] at h
  exact Eq.symm h |>.trans (by abel)

end InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

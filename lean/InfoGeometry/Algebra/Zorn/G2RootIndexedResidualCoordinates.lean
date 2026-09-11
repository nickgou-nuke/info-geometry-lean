/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2PositiveRootsInvariance

namespace InfoGeometry.Algebra.Zorn.G2RootIndexedResidualCoordinates

open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2Roots

/-- Boolean residual coordinates indexed by the positive roots inverted by the
    coordinate-level Coxeter word associated to `w`. -/
abbrev ResidualExponent (w : WeylG2) :=
  { α : G2PositiveRoot // α ∈ inversionRoots w } → Bool

/-- Cardinality of the residual exponent space - a direct consequence of the bijection with
    functions `Fin n → Bool`. -/
theorem residualExponent_card (w : WeylG2) :
    Fintype.card (ResidualExponent w) =
      2 ^ (inversionRoots w).card := by
  classical
  simp [ResidualExponent]

theorem residualExponent_one_card :
    Fintype.card (ResidualExponent (0, false)) = 1 := by
  rw [residualExponent_card]
  rw [inversionRoots_one]
  rfl

end InfoGeometry.Algebra.Zorn.G2RootIndexedResidualCoordinates

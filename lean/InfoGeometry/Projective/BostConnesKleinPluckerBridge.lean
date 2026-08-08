import InfoGeometry.Canonical.BostConnesKMS
import InfoGeometry.Projective.KleinQuadricPlucker

namespace InfoGeometry.Projective.BostConnesKleinPluckerBridge

open InfoGeometry.Arithmetic.BostConnesSystem
open InfoGeometry.Canonical.BostConnesKMS
open KleinQuadricPlucker

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (C : BostConnesCuntzSystem Op)

/-- The correct KMS range projectors for the Bost-Connes system. -/
def kmsProjector (n : ℕ+) : Op :=
  S C n * star (S C n)

/--
Construct the six ordered Plücker-coordinate candidates from four KMS range
projectors.  No commutativity is asserted by this definition.
-/
def projectorPlucker (n0 n1 n2 n3 : ℕ+) : Plucker6 Op where
  p01 := kmsProjector C n1 - kmsProjector C n0
  p02 := kmsProjector C n2 - kmsProjector C n0
  p03 := kmsProjector C n3 - kmsProjector C n0
  p12 := kmsProjector C n2 - kmsProjector C n1
  p13 := kmsProjector C n3 - kmsProjector C n1
  p23 := kmsProjector C n3 - kmsProjector C n2

/--
The ordered difference-Plücker expression is the sum of three commutator
defects.  Hence it vanishes when `e₁`, `e₂`, and `e₃` commute.  The base point
`e₀` cancels without an additional property.
-/
theorem differencePlucker_on_klein_of_commute
    {A : Type*} [Ring A] (e0 e1 e2 e3 : A)
    (h12 : Commute e1 e2) (h13 : Commute e1 e3) (h23 : Commute e2 e3) :
    (e1 - e0) * (e3 - e2) - (e2 - e0) * (e3 - e1) +
        (e3 - e0) * (e2 - e1) = 0 := by
  calc
    (e1 - e0) * (e3 - e2) - (e2 - e0) * (e3 - e1) +
          (e3 - e0) * (e2 - e1) =
        (e1 * e3 - e3 * e1) + (e2 * e1 - e1 * e2) +
          (e3 * e2 - e2 * e3) := by noncomm_ring
    _ = 0 := by rw [h13.eq, h12.eq, h23.eq]; noncomm_ring

/--
BUCKET 2 (conditional): four Bost--Connes range projectors determine ordered
Plücker coordinates on the Klein quadric whenever the representation's range
projections are Nica covariant (i.e. satisfy the meet law).

The owner debt of constructing `RangeProjectionsCommute C` is discharged by 
`rangeProjectionsCommute_of_isNicaCovariant`. However, constructing Nica 
covariance for a concrete representation remains open.
-/
theorem projectorPlucker_on_klein_of_nica
    (hNica : CuntzMultiplicativeIndexing.IsNicaCovariant C) (n0 n1 n2 n3 : ℕ+) :
    let P := projectorPlucker C n0 n1 n2 n3
    P.p01 * P.p23 - P.p02 * P.p13 + P.p03 * P.p12 = 0 := by
  have hCore : CuntzMultiplicativeIndexing.RangeProjectionsCommute C := CuntzMultiplicativeIndexing.rangeProjectionsCommute_of_isNicaCovariant C hNica
  dsimp [projectorPlucker]
  -- Note: kmsProjector is exactly C.rangeProjection.
  have hComm (n m : ℕ+) : Commute (kmsProjector C n) (kmsProjector C m) := by
    change Commute (C.rangeProjection n) (C.rangeProjection m)
    exact hCore n m
  exact differencePlucker_on_klein_of_commute
    (kmsProjector C n0) (kmsProjector C n1)
    (kmsProjector C n2) (kmsProjector C n3)
    (hComm n1 n2) (hComm n1 n3) (hComm n2 n3)

end InfoGeometry.Projective.BostConnesKleinPluckerBridge

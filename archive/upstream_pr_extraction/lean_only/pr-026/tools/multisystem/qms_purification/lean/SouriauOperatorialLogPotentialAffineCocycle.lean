import Mathlib

/-!
QMS isolated proof target for purifying
`partitionPotentialAffineCorrectionClaim` in
`InfoGeometry.Canonical.SouriauOperatorialLogPotential`.

Mathematical context:
- `State` is the state carrier.
- `LieGroup` is an abstract group/action carrier with multiplication.
- `LieAlgebra` is the parameter carrier.
- `LieDual` is the moment-map/cocycle carrier with addition.
- `LieCovarianceAndCocycle` supplies:
  - a Souriau thermodynamic datum with moment map `J`;
  - a state action `groupAction`;
  - a coadjoint action on moment values;
  - an affine cocycle `c : G → 𝔤*`;
  - strict equivariance of the moment map;
  - the cocycle law `c(gh) = g⋅c(h) + c(g)`.

Existing mathlib/literature context:
- Mathlib supplies equality and the algebraic operations `[Mul LieGroup]` and
  `[Add LieDual]` used by the cocycle identity.
- In Souriau affine coadjoint thermodynamics, partition-potential affine
  corrections require additional transformed-potential/readout fields that are
  absent from this owner surface.

QMS purification move:
- Replace the impossible partition-potential analytic socket by the explicit
  affine cocycle theorem already carried by the structure.
-/

namespace InfoGeometry.QMS.SouriauOperatorialLogPotentialAffineCocycle

structure SouriauLieThermoData (State LieAlgebra LieDual : Type*) where
  momentMap : State → LieDual

structure LieCovarianceAndCocycle
    (State LieGroup LieAlgebra LieDual : Type*) [Mul LieGroup] [Add LieDual] where
  souriau : SouriauLieThermoData State LieAlgebra LieDual
  groupAction : LieGroup → State → State
  coadjointAction : LieGroup → LieDual → LieDual
  betaAction : LieGroup → LieAlgebra → LieAlgebra
  cocycle : LieGroup → LieDual
  strictEquivariance :
    ∀ g x, souriau.momentMap (groupAction g x) = coadjointAction g (souriau.momentMap x)
  affineCocycle :
    ∀ g h, cocycle (g * h) = coadjointAction g (cocycle h) + cocycle g

/-- The affine-correction socket reduces to the supplied Souriau cocycle law. -/
theorem partitionPotentialAffineCorrection_as_cocycle_law
    {State LieGroup LieAlgebra LieDual : Type*} [Mul LieGroup] [Add LieDual]
    (L : LieCovarianceAndCocycle State LieGroup LieAlgebra LieDual)
    (g h : LieGroup) :
    L.cocycle (g * h) = L.coadjointAction g (L.cocycle h) + L.cocycle g := by
  exact L.affineCocycle g h

end InfoGeometry.QMS.SouriauOperatorialLogPotentialAffineCocycle

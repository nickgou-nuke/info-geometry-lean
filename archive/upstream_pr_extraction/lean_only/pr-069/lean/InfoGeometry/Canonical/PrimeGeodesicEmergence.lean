import InfoGeometry.Canonical.KleinBottleOrientifold
import InfoGeometry.Canonical.PrimeGasMaxEnt
import InfoGeometry.Clifford.HestenesDirac
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.PrimeGeodesicEmergence

Prime-orbit emergence packet for the Cl(1,1) / prime-gas corridor.

This file keeps the geometric claim constructive:

- the boost generator is a real bivector axis,
- the orbit labels are explicit natural-number data,
- the prime-label property is a property,
- the energy readout is `log n`,
- the Klein bottle orientifold is carried separately as a filter packet.

No claim is made here that the primes have already been proved from the
geometry; this file records the exact packet one would need to do so.
-/

namespace InfoGeometry.Canonical.PrimeGeodesicEmergence

open KleinBottleOrientifold
open PrimeGasMaxEnt
open InfoGeometry.Clifford.HestenesDirac

universe u

/-- A discrete orbit label together with its primitive/irreducible status. -/
@[rep_depth transport]
abbrev PrimeGeodesicOrbit := {n : ℕ // Nat.Prime n}

namespace PrimeGeodesicOrbit

abbrev label (o : PrimeGeodesicOrbit) : ℕ := o.1
abbrev primeLabel (o : PrimeGeodesicOrbit) : Nat.Prime o.label := o.2

/-- The boost-energy readout of the orbit. -/
@[rep_depth transport]
noncomputable def energy (o : PrimeGeodesicOrbit) : ℝ :=
  Real.log o.label

@[rep_depth transport]
theorem energy_eq_log_label (o : PrimeGeodesicOrbit) :
    o.energy = Real.log o.label := rfl

@[rep_depth transport]
theorem squarefree_label (o : PrimeGeodesicOrbit) :
    Squarefree o.label :=
  o.primeLabel.squarefree

end PrimeGeodesicOrbit

set_option linter.dupNamespace false in
/--
Cl(1,1)-style prime-orbit emergence packet.

The boost bivector is explicit, the discrete orbit is explicit, and the
orientifold filter is explicit.  The number-theoretic output remains a packet
of hypotheses rather than a fake theorem.
-/
@[rep_depth transport]
structure PrimeGeodesicEmergence
    (A : Type u) [Mul A] [One A] [Neg A] where
  spacetime : RealSpacetimeAlgebra A
  boostBivector : A
  boostBivector_sq : boostBivector * boostBivector = 1
  orbit : PrimeGeodesicOrbit
  orientifold : KleinBottleOrientifold

end InfoGeometry.Canonical.PrimeGeodesicEmergence

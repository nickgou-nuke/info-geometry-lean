import InfoGeometry.Canonical.PrimeGasMaxEnt
import InfoGeometry.Clifford.HestenesDirac
import InfoGeometry.Meta.Architecture
import InfoGeometry.Topology.V4RootSystem
import InfoGeometry.Topology.ProjectiveKleinCompactification
import InfoGeometry.BostConnes.BostConnesParity

/-!
# InfoGeometry.Canonical.KleinBottleOrientifold

Topological orientifold packet for the prime-gas lane.

The purpose of this module is not to prove that the Klein bottle literally
creates the Möbius function.  The purpose is to package, in a kernel-safe way,
the precise hypotheses one needs to represent:

- a `V4` Weyl quotient,
- an orientation-reversing filter,
- a fermion-parity projection,
- and the square-killing support condition that singles out square-free
  occupancy patterns.

Those claims remain explicit hypotheses until a concrete geometric/Fock model
instantiates them.
-/

namespace InfoGeometry.Canonical.KleinBottleOrientifold

open InfoGeometry.Topology
open PrimeGasMaxEnt
open InfoGeometry.Clifford.HestenesDirac

universe u

/-!
The finite orientifold carrier is the actual involutive element of the
repo-owned Klein-four group.  The former record only stored unrelated `Prop`
markers and reflexive equalities; the projective Klein and Möbius laws are
owned by `ProjectiveKleinCompactification` and are not duplicated here.
-/
abbrev KleinBottleOrientifold :=
  {g : InfoGeometry.Topology.V4RootSystem.V4Group //
    g * g = InfoGeometry.Topology.V4RootSystem.V4Group.I}

/-- Canonical point-inversion carrier for the finite orientifold lane. -/
def canonicalKleinBottleOrientifold : KleinBottleOrientifold :=
  ⟨InfoGeometry.Topology.V4RootSystem.V4Group.W12,
    InfoGeometry.Topology.V4RootSystem.v4_point_inversion_involution⟩

@[simp]
theorem canonicalKleinBottleOrientifold_value :
    (canonicalKleinBottleOrientifold : KleinBottleOrientifold).1 =
      InfoGeometry.Topology.V4RootSystem.V4Group.W12 :=
  rfl

@[simp]
theorem canonicalKleinBottleOrientifold_projective_klein_mobius (t : ℚ) :
    ProjectiveKleinCompactification.ProjectivelyEqual
        ProjectiveKleinCompactification.I2
        ProjectiveKleinCompactification.minusI2 ∧
      ProjectiveKleinCompactification.twistA *
          ProjectiveKleinCompactification.parabolicB *
          ProjectiveKleinCompactification.twistA *
          ProjectiveKleinCompactification.parabolicB =
        ProjectiveKleinCompactification.I2 ∧
      ProjectiveKleinCompactification.mobiusS.mulVec ![t, 1] = ![-1, t] ∧
      ProjectiveKleinCompactification.ProjectivelyEqual
        (ProjectiveKleinCompactification.mobiusS *
          ProjectiveKleinCompactification.mobiusS)
        ProjectiveKleinCompactification.I2 :=
  ProjectiveKleinCompactification.projective_klein_formula_packet t

/--
Bridge packet tying the prime-gas MaxEnt data to the Klein bottle orientifold
hypotheses.

This is the topological filter surface: the prime gas remains a Jaynes packet,
and the orientifold effect remains an explicit hypothesis block.
-/
@[rep_depth transport]
structure OrientifoldPrimeGasPacket (D : PrimeGasJaynesData) where
  orientifold : KleinBottleOrientifold
  primeGas : PrimeGasJaynesData.PrimeGasJaynesConjecture D

/--
Topological support packet for the square-free sector.

This keeps the square-killing claim as a theorem-shaped surface rather than
as a kernel axiom.
-/
@[rep_depth transport]
structure SquareFreeSupportPacket where
  label : ℕ
  squareFree : Squarefree label

end InfoGeometry.Canonical.KleinBottleOrientifold

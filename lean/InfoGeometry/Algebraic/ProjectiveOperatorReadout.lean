import Mathlib.GroupTheory.GroupAction.Defs
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Basic
import InfoGeometry.Algebraic.RealModularReadout

/-!
InfoGeometry/Algebraic/ProjectiveOperatorReadout.lean

Operator-first projective readout layer.
No coordinates. No complex substrate.
-/

noncomputable section

namespace InfoGeometry.Algebraic

open Filter
open scoped Topology

/--
A projective operator action over a base action.

`G` acts on the base `X`.
`R` is the rotor/phase/cocycle group.
`Op` is the operator group acting on the carrier, for example units of an
endomorphism algebra or a Clifford/Krein operator group.

The projective law is

`U(gh, x) = phase(C(g, h • x)) * U(g, h • x) * U(h, x)`.

No coordinate model is part of this definition.
-/
structure ProjectiveOperatorReadout
    (G X R Op : Type*)
    [Group G] [MulAction G X] [Group R] [Group Op] where
  cocycle : MulActionCocycle G X R
  phase : R →* Op
  op : G → X → Op
  op_one : ∀ x, op 1 x = 1
  op_mul :
    ∀ g h x,
      op (g * h) x =
        phase (cocycle g (h • x)) * op g (h • x) * op h x

namespace ProjectiveOperatorReadout

variable
    {G X R Op : Type*}
    [Group G] [MulAction G X] [Group R] [Group Op]

/--
The stabilizer rotor anomaly.

At a fixed point, the base dependence in the cocycle collapses to a genuine
group homomorphism.
-/
def stabilizerRotorHom
    (P : ProjectiveOperatorReadout G X R Op)
    (x : X) :
    MulAction.stabilizer G x →* R where
  toFun h := P.cocycle (h : G) x
  map_one' := by
    simpa using P.cocycle.map_one x
  map_mul' h k := by
    have hk : (k : G) • x = x := k.property
    simpa [hk] using P.cocycle.map_mul (h : G) (k : G) x

/--
The operator-level stabilizer anomaly obtained by applying the readout
`phase : R →* Op`.
-/
def stabilizerPhaseHom
    (P : ProjectiveOperatorReadout G X R Op)
    (x : X) :
    MulAction.stabilizer G x →* Op :=
  P.phase.comp (P.stabilizerRotorHom x)

end ProjectiveOperatorReadout

end InfoGeometry.Algebraic

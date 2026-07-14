import InfoGeometry.Categorical.FibonacciSelfDualCarrier
import InfoGeometry.Canonical.BulkBoundaryZeroModeOwner

/-!
# InfoGeometry.Categorical.FibonacciMajoranaBoundaryCarrier

Stage-4 bridge from the Fibonacci self-dual carrier socket to the existing
Majorana bulk-boundary zero-mode owner.

This file does not construct an O(5,5) representation or identify every
Fibonacci braid observable with a boundary Majorana operator.  It records the
safe combined readout currently supported by the repo:

* the Fibonacci carrier has a Hilbert self-dual cone;
* the installed boundary owner gives an actual nonzero kernel witness for the
  open-chain operator.
-/

noncomputable section

open scoped InnerProductSpace

namespace FibonacciMajoranaBoundaryCarrier

open InfoGeometry.Categorical.FibonacciSelfDualCarrier
open InfoGeometry.Canonical.BulkBoundaryZeroModeOwner
open InfoGeometry.Quantum.BulkBoundary
open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.Quantum.RealMajorana

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A : Type*} [Semiring A]

variable {S : Type v} [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]

local notation "EndS" => S →L[ℝ] S

/--
Combined carrier/zero-mode readout:
a Fibonacci carrier supplies the self-dual cone, and the Majorana
bulk-boundary owner supplies a genuine surface zero mode.
-/
theorem carrier_selfDualCone_and_boundary_zeroMode
    (C : Carrier (E := E) A)
    {M : RealMajoranaDatum (S := S)}
    {P0 : KPolarization (S := S) M}
    {localOp : KitaevCell → EndS}
    {chain : List KitaevCell}
    (O : DimensionAgnosticBoundaryZeroModeOwner
      (S := S) M P0 localOp chain) :
    ProperCone.innerDual (C.positiveCone.cone : Set E) = C.positiveCone.cone ∧
      HasZeroMode (S := S)
        (globalChainOperatorFromOpenChain (S := S) localOp chain) :=
  ⟨C.positiveCone_innerDual_eq, owner_hasZeroMode O⟩

/--
Explicit witness form of the same bridge: the carrier cone is self-dual and
the boundary owner produces a nonzero vector in the open-chain kernel.
-/
theorem carrier_selfDualCone_and_exists_boundary_zeroMode
    (C : Carrier (E := E) A)
    {M : RealMajoranaDatum (S := S)}
    {P0 : KPolarization (S := S) M}
    {localOp : KitaevCell → EndS}
    {chain : List KitaevCell}
    (O : DimensionAgnosticBoundaryZeroModeOwner
      (S := S) M P0 localOp chain) :
    ProperCone.innerDual (C.positiveCone.cone : Set E) = C.positiveCone.cone ∧
      ∃ v : S,
        (globalChainOperatorFromOpenChain (S := S) localOp chain) v = 0 ∧ v ≠ 0 :=
  ⟨C.positiveCone_innerDual_eq, owner_exists_zeroMode O⟩

end FibonacciMajoranaBoundaryCarrier

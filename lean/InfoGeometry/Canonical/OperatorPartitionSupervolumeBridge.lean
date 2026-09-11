import InfoGeometry.Canonical.SouriauConformalKKTContext
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CartanBerezinianCore

/-!
# InfoGeometry.Canonical.OperatorPartitionSupervolumeBridge

Small truthful finite-shadow bridge from the operatorial Souriau/Weyl partition
lane to the existing super-volume/Berezinian lane.

This file does NOT claim that the partition is definitionally the Berezinian.
Instead it exposes the smallest honest theorem surface available now:
if the caller supplies an explicit witness identifying the operatorial partition
with the generalized Berezinian scale, then the operatorial Massieu potential is
exactly the logarithm of that super-volume quantity.

Boundary: `generalizedBerezinianScale` is owned by `CartanBerezinianCore` and
currently requires `[FiniteDimensional ℝ H]` because it is defined via determinant
volume characters.  Therefore this module is an exact finite-dimensional
Berezinian shadow of the operatorial partition lane, not the full
dimension-agnostic Type III/operator-volume theorem.
-/

namespace InfoGeometry.Canonical.OperatorPartitionSupervolumeBridge

open InfoGeometry.Canonical.SouriauConformalKKT
open InfoGeometry.Canonical.CartanBerezinianCore

section Core

variable {α : Type _}
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [FiniteDimensional ℝ H]

namespace ConformalGibbsSouriauOperatorContext

/--
Exact log-supervolume bridge from an explicit partition/Berezinian witness.

This is the smallest truthful theorem currently available between the two lanes:
- operatorial thermodynamic partition/Massieu, and
- generalized Berezinian super-volume scale.

It remains a finite-dimensional determinant-volume shadow because the
`generalizedBerezinianScale` owner carries `[FiniteDimensional ℝ H]`.
-/
@[rep_depth transport]
theorem operatorMassieu_eq_log_generalizedBerezinianScale_of_operatorPartition_eq_generalizedBerezinianScale
    (C : ConformalGibbsSouriauOperatorContext (α := α) (H := H))
    (S : SchurAdmissibleTransport (E := H))
    (hPartition : C.operatorPartition = generalizedBerezinianScale (E := H) S) :
    C.operatorMassieu = Real.log (generalizedBerezinianScale (E := H) S) := by
  calc
    C.operatorMassieu = Real.log C.operatorPartition := C.operatorMassieu_eq_log_partition
    _ = Real.log (generalizedBerezinianScale (E := H) S) := by rw [hPartition]

end ConformalGibbsSouriauOperatorContext

end Core

end InfoGeometry.Canonical.OperatorPartitionSupervolumeBridge

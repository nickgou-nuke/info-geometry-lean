import Mathlib.Data.Matrix.Basic
import InfoGeometry.Singular.Drazin

/-!
# Drazin anomaly readouts for the split-spinor boundary

This module keeps the `32 × 32` split-spinor notation used by the transport
lane, but it does not manufacture a kernel-dimension index.  The actual Drazin
laws are carried by `InfoGeometry.Singular.Drazin.IsDrazinInverse`; the chiral
anomaly index is an explicit readout attached to such a witness.
-/

namespace InfoGeometry.Canonical.DrazinAnomaly

open InfoGeometry.Singular.Drazin

/-- The concrete `32 × 32` real split-spinor operator type. -/
abbrev SpinorOp : Type :=
  Matrix (Fin 32) (Fin 32) ℝ

/--
The split chiral grading matrix: `+1` on the first half and `-1` on the second
half of the `Fin 32` basis.
-/
def Gamma_11 : SpinorOp :=
  fun i j => if i = j then (if i.val < 16 then 1 else -1) else 0

/--
An operator is Drazin-defective at index `k` when it has a Drazin inverse
witness at that index.

This is intentionally not `True`: users must provide an actual Drazin inverse
certificate from the singular/Drazin owner.
-/
def is_drazin_defective (Op : SpinorOp) (k : ℕ) : Prop :=
  ∃ D : SpinorOp, IsDrazinInverse Op D k

/--
Proof-carrying anomaly readout.

`anomalyIndex` is a calibrated integer readout attached to an actual Drazin
witness.  Computing it as a difference of chiral kernel dimensions is separate
closure debt; this packet prevents that missing construction from being hidden
behind a fake definition.
-/
structure DrazinAnomalyReadout (Γ Op : SpinorOp) (k : ℕ) where
  drazinInverse : SpinorOp
  drazinProof : IsDrazinInverse Op drazinInverse k
  anomalyIndex : ℤ

namespace DrazinAnomalyReadout

variable {Γ Op : SpinorOp} {k : ℕ}

/-- A readout exposes the underlying Drazin-defect witness. -/
theorem is_drazin_defective (R : DrazinAnomalyReadout Γ Op k) :
    InfoGeometry.Canonical.DrazinAnomaly.is_drazin_defective Op k :=
  ⟨R.drazinInverse, R.drazinProof⟩

end DrazinAnomalyReadout

/-- Integer anomaly readout extracted from a proof-carrying Drazin packet. -/
def drazin_anomaly_index {Γ Op : SpinorOp} {k : ℕ}
    (R : DrazinAnomalyReadout Γ Op k) : ℤ :=
  R.anomalyIndex

end InfoGeometry.Canonical.DrazinAnomaly

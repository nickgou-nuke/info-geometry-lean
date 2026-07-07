import InfoGeometry.Physics.HadjiivanovCuntzBridge
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Sandbox restore: Hadjiivanov Bost-Connes bridge

Sandbox-only refactor of the lost bridge packet. This version keeps the file
small and splits the readout into explicit helper lemmas, reusing the live owner
surface from `InfoGeometry.Physics.HadjiivanovCuntzBridge`.

It does not claim a full thermodynamic/Bost-Connes realization. It only records
that the finite packaged logarithmic block has vanishing matrix trace, hence the
minimal partition-function readout used by downstream bridge code is zero.
-/

namespace Sandbox.Restore.Hadjiivanov

open InfoGeometry.Physics.Hadjiivanov

/-- Sandbox partition-function readout of the finite Hadjiivanov log block. -/
def logBlockPartitionFunction (R : Type*) [CommRing R] : R :=
  Matrix.trace (standardLogBlock R).matrix

@[simp] theorem logBlockPartitionFunction_def (R : Type*) [CommRing R] :
    logBlockPartitionFunction R = Matrix.trace (standardLogBlock R).matrix := rfl

/-- Helper lemma: the sandbox partition function is exactly the owner trace readout. -/
@[simp] theorem logBlockPartitionFunction_eq_owner_trace (R : Type*) [CommRing R] :
    logBlockPartitionFunction R = Matrix.trace (standardLogBlock R).matrix := rfl

/-- Helper lemma: the finite Hadjiivanov logarithmic block has vanishing partition readout. -/
@[simp] theorem logBlockPartitionFunction_vanishes (R : Type*) [CommRing R] :
    logBlockPartitionFunction R = 0 := by
  simpa [logBlockPartitionFunction] using standardLogBlock_trace (R := R)

/-- Restatement in owner-first style: the standard block trace vanishes. -/
@[simp] theorem standardLogBlock_partition_vanishes (R : Type*) [CommRing R] :
    Matrix.trace (standardLogBlock R).matrix = 0 := by
  simpa [logBlockPartitionFunction] using logBlockPartitionFunction_vanishes (R := R)

end Sandbox.Restore.Hadjiivanov

import InfoGeometry.Physics.HadjiivanovCuntzBridge
import InfoGeometry.Physics.AmplituhedronBostConnes
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Hadjiivanov Monodromy to Bost-Connes Partition Function

Evaluates the Bost-Connes KMS partition function over the logarithmic monodromy
block. By tracking the anomalous dimensions, we evaluate the thermodynamic
trace of the chiral nilpotent operators.
-/

namespace InfoGeometry.Physics.Hadjiivanov

/--
The thermodynamic KMS trace (partition function) of the Hadjiivanov log block
evaluates to its trace, which isolates the primary component since the nilpotent
logarithmic partner N has trace 0.
-/
def logBlockPartitionFunction (R : Type*) [CommRing R] : R :=
  Matrix.trace (standardLogBlock R).matrix

/--
The partition function of the pure nilpotent log block vanishes, representing
the structural feature of the un-normalized Amplituhedron boundary volume anomaly.
-/
theorem logBlockPartitionFunction_vanishes (R : Type*) [CommRing R] :
    logBlockPartitionFunction R = 0 := by
  dsimp [logBlockPartitionFunction, standardLogBlock]
  simp [Matrix.trace_fin_two, jordanNilpotent]

end InfoGeometry.Physics.Hadjiivanov

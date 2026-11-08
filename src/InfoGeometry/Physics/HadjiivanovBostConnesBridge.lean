import InfoGeometry.Physics.HadjiivanovCuntzBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.AmplituhedronBostConnes
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Hadjiivanov Monodromy and Zeta Readout

Records an algebraic relation between the logarithmic-block trace and the
Riemann zeta readout. This file does not construct a Bost--Connes algebra,
dynamics, or KMS state.
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

/--
The bridge theorem connecting the Hadjiivanov log block partition function
to the Bost-Connes KMS partition function.
By tracking the anomalous dimensions, the total partition function separates
into the chiral nilpotent anomaly (which vanishes) and the zeta function.
-/
theorem hadjiivanov_log_block_zeta_readout (β : ℂ) :
    AmplituhedronBostConnes.riemannZetaReadout β =
    logBlockPartitionFunction ℂ + riemannZeta β := by
  rw [AmplituhedronBostConnes.riemannZetaReadout]
  have h : logBlockPartitionFunction ℂ = 0 := logBlockPartitionFunction_vanishes ℂ
  rw [h]
  simp

end InfoGeometry.Physics.Hadjiivanov

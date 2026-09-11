import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.TopologicalStandardModelBridge
import InfoGeometry.Canonical.TrialitySpin8Permutations

/-!
# Three-cycle / triality structural bridge for a QCD-facing lane

The repository already contains two independent finite three-cycles:

* the `TripotentState` cycle used by the quark-ladder indexing bridge;
* the canonical Spin(8)-label triality permutation on `Fin 3`.

This file packages their exact order-three behaviour side by side.  It does
**not** identify either three-cycle with the three physical fermion generations
and does not prove an Albert-algebra generation theorem.
-/

namespace InfoGeometry.Physics.QCDTrialityStructuralBridge

open InfoGeometryCore
open InfoGeometry.Physics
open InfoGeometry.Canonical.TrialitySpin8Permutations

/-- The repository's tripotent index advances by one modulo three while the
canonical triality permutation closes after three applications. -/
theorem finite_triality_cycle_packet (s : TripotentState) :
    (tripotentStateIndex (TripotentState.trialityCycle s)).val =
        (tripotentStateIndex s + 1) % 3 ∧
      trialityCycle ^ 3 = (1 : Equiv.Perm TrialitySector) :=
  ⟨tripotent_state_index_cycle s, trialityCycle_pow_three⟩

/-- Transport of the three canonical triality sector seeds closes after one
full triality orbit. -/
theorem triality_seed_transport_closes
    (p : InfoGeometry.Clifford.ConformalLift55.ConformalNullPair)
    (s : TrialitySector) :
    trialitySectorSeed p ((trialityCycle ^ 3) s) =
      trialitySectorSeed p s :=
  trialitySectorTransport_cube_id p s

end InfoGeometry.Physics.QCDTrialityStructuralBridge

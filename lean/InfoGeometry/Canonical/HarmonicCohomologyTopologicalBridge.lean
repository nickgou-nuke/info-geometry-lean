import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Canonical.HarmonicRepresentativeCohomologyProjectionBridge
import InfoGeometry.Canonical.DeRhamCohomologyQuotientTopologicalBridge

/-!
# Topology of the harmonic representative projection

The harmonic-to-cohomology map is algebraically owned by
`HarmonicRepresentativeCohomologyProjectionBridge`.  Here we factor it as a
continuous inclusion into closed forms followed by the native de Rham quotient
projection.  Continuity uses only the subtype topologies and the quotient
topology; no Hodge-theoretic analytic assertion is added.
-/

noncomputable section

namespace InfoGeometry.Canonical.HarmonicCohomologyTopologicalBridge

open CategoryTheory
open ExteriorAlgebra
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.DeRhamCohomologyQuotientTopologicalBridge
open InfoGeometry.Canonical.HarmonicRepresentativeCohomologyProjectionBridge
open InfoGeometry.Canonical.HodgeIsomorphismHarmonicBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The harmonic submodule included into the closed-form carrier. -/
def harmonicToClosedMap
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (h_closed : ∀ w ∈ harmonicSubmodule d dstar, d w = 0) :
    harmonicSubmodule d dstar → LinearMap.ker d :=
  fun w => ⟨w.1, h_closed w.1 w.2⟩

theorem continuous_harmonicToClosedMap
    [TopologicalSpace (ExteriorAlgebra R V)]
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (h_closed : ∀ w ∈ harmonicSubmodule d dstar, d w = 0) :
    Continuous (harmonicToClosedMap d dstar h_closed) := by
  apply Continuous.subtype_mk continuous_subtype_val

theorem continuous_harmonicToCohomology
    [TopologicalSpace (ExteriorAlgebra R V)]
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (h_closed : ∀ w ∈ harmonicSubmodule d dstar, d w = 0) :
    Continuous (harmonicToCohomologyLinearMap d dstar h_closed) := by
  have h_cont :=
    (continuous_deRhamQuotientMk d).comp
      (continuous_harmonicToClosedMap d dstar h_closed)
  simpa [harmonicToCohomologyLinearMap, harmonicToClosedMap] using h_cont

/-- The harmonic representative projection as a `TopCat` morphism. -/
def harmonicToCohomologyTopCat
    [TopologicalSpace (ExteriorAlgebra R V)]
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (h_closed : ∀ w ∈ harmonicSubmodule d dstar, d w = 0) :
    TopCat.of (harmonicSubmodule d dstar) ⟶ deRhamQuotientTopCat d :=
  TopCat.ofHom
    { toFun := harmonicToCohomologyLinearMap d dstar h_closed
      continuous_toFun := continuous_harmonicToCohomology d dstar h_closed }

end InfoGeometry.Canonical.HarmonicCohomologyTopologicalBridge

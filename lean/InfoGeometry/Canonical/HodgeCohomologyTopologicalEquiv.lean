import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Canonical.HarmonicCohomologyTopologicalBridge
import InfoGeometry.Canonical.HodgeDecompositionHarmonicSurjectivityBridge

/-!
# Conditional topological Hodge equivalence

The algebraic Hodge owner supplies a `LinearEquiv` from harmonic forms to de
Rham cohomology under an explicit decomposition hypothesis.  This file
promotes it to a `Homeomorph` when continuity of the inverse is supplied.
The forward continuity is derived from the harmonic projection bridge.
-/

noncomputable section

namespace InfoGeometry.Canonical.HodgeCohomologyTopologicalEquiv

open CategoryTheory
open ExteriorAlgebra
open InfoGeometry.Canonical.DeRhamCohomologyQuotientTopologicalBridge
open InfoGeometry.Canonical.HarmonicCohomologyTopologicalBridge
open InfoGeometry.Canonical.HarmonicRepresentativeCohomologyProjectionBridge
open InfoGeometry.Canonical.HodgeDecompositionHarmonicSurjectivityBridge
open InfoGeometry.Canonical.HodgeIsomorphismHarmonicBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The algebraic Hodge decomposition equivalence, equipped with the quotient
topology and an explicitly supplied continuity proof for its inverse. -/
def hodgeDecompositionHomeomorph
    [TopologicalSpace (ExteriorAlgebra R V)]
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (h_closed : ∀ w ∈ harmonicSubmodule d dstar, d w = 0)
    (h_coclosed : ∀ w ∈ harmonicSubmodule d dstar, dstar w = 0)
    (inner : ExteriorAlgebra R V → ExteriorAlgebra R V → R)
    (h_pos : ∀ x, inner x x = 0 → x = 0)
    (h_adj : ∀ α w, inner (d α) w = inner α (dstar w))
    (h_zero : ∀ α, inner α 0 = 0)
    (h_decomp : ∀ w : LinearMap.ker d,
      ∃ alpha : ExteriorAlgebra R V, ∃ h : harmonicSubmodule d dstar,
        w.1 = d alpha + h.1)
    (h_inv : Continuous
      ((hodgeDecompositionLinearEquiv d dstar h_closed h_coclosed inner h_pos
        h_adj h_zero h_decomp).symm)) :
    harmonicSubmodule d dstar ≃ₜ deRhamQuotient d :=
  Homeomorph.mk
    (hodgeDecompositionLinearEquiv d dstar h_closed h_coclosed inner h_pos
      h_adj h_zero h_decomp).toEquiv
    (continuous_harmonicToCohomology d dstar h_closed)
    h_inv

@[simp] theorem hodgeDecompositionHomeomorph_apply
    [TopologicalSpace (ExteriorAlgebra R V)]
    (d dstar : Module.End R (ExteriorAlgebra R V))
    (h_closed : ∀ w ∈ harmonicSubmodule d dstar, d w = 0)
    (h_coclosed : ∀ w ∈ harmonicSubmodule d dstar, dstar w = 0)
    (inner : ExteriorAlgebra R V → ExteriorAlgebra R V → R)
    (h_pos : ∀ x, inner x x = 0 → x = 0)
    (h_adj : ∀ α w, inner (d α) w = inner α (dstar w))
    (h_zero : ∀ α, inner α 0 = 0)
    (h_decomp : ∀ w : LinearMap.ker d,
      ∃ alpha : ExteriorAlgebra R V, ∃ h : harmonicSubmodule d dstar,
        w.1 = d alpha + h.1)
    (h_inv : Continuous
      ((hodgeDecompositionLinearEquiv d dstar h_closed h_coclosed inner h_pos
        h_adj h_zero h_decomp).symm))
    (w : harmonicSubmodule d dstar) :
    hodgeDecompositionHomeomorph d dstar h_closed h_coclosed inner h_pos h_adj
      h_zero h_decomp h_inv w =
      harmonicToCohomologyLinearMap d dstar h_closed w :=
  rfl

end InfoGeometry.Canonical.HodgeCohomologyTopologicalEquiv

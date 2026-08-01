import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Constructions
import InfoGeometry.Canonical.BRSTQuotientInnerProductLiftBridge

/-!
# Topology of the algebraic BRST quotient

This file adds only the quotient topology to the already defined algebraic
quotient `ker q / im q`.  No topology or analytic property is assigned to the
BRST differential itself.  The universal quotient map and the standard
continuous descent principle are exposed for later colimit constructions.
-/

noncomputable section

namespace InfoGeometry.Canonical.BRSTQuotientTopologicalBridge

open InfoGeometry.Canonical.BRSTQuotientInnerProductLiftBridge

variable {R H Y : Type*} [CommRing R] [AddCommGroup H] [Module R H]

abbrev BRSTSubmodule (q : Module.End R H) : Submodule R (LinearMap.ker q) :=
  (LinearMap.range q).comap (LinearMap.ker q).subtype

abbrev BRSTQuotient (q : Module.End R H) :=
  LinearMap.ker q ⧸ BRSTSubmodule q

/-- The canonical projection from closed states to BRST cohomology. -/
def brstQuotientMk (q : Module.End R H) : LinearMap.ker q → BRSTQuotient q :=
  Submodule.Quotient.mk

theorem continuous_brstQuotientMk
    [TopologicalSpace H] (q : Module.End R H) :
    Continuous (brstQuotientMk q) := by
  change Continuous (Submodule.Quotient.mk : LinearMap.ker q →
    LinearMap.ker q ⧸ BRSTSubmodule q)
  exact continuous_quotient_mk'

/-- A continuous map on closed states descends through the BRST quotient when
it is invariant under the quotient relation. -/
theorem continuous_brstQuotient_lift
    [TopologicalSpace H] [TopologicalSpace Y]
    (q : Module.End R H)
    (f : LinearMap.ker q → Y)
    (hf : Continuous f)
    (h_invariant : ∀ a b : LinearMap.ker q,
      (BRSTSubmodule q).quotientRel a b →
        f a = f b) :
    Continuous (Quotient.lift f h_invariant : BRSTQuotient q → Y) := by
  exact hf.quotient_lift h_invariant

end InfoGeometry.Canonical.BRSTQuotientTopologicalBridge

import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge

/-!
# Topology of the algebraic de Rham quotient

The de Rham owner defines cohomology algebraically as `ker d / im d`.
This companion only installs the native quotient topology and packages its
projection in `TopCat`; it does not add a smooth, measure-theoretic, or
analytic structure to the differential.
-/

noncomputable section

namespace InfoGeometry.Canonical.DeRhamCohomologyQuotientTopologicalBridge

open CategoryTheory
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge

variable {R V Y : Type*} [CommRing R] [AddCommGroup V] [Module R V]

abbrev deRhamSubmodule
    (d : Module.End R (ExteriorAlgebra R V)) :
    Submodule R (LinearMap.ker d) :=
  (LinearMap.range d).comap (LinearMap.ker d).subtype

abbrev deRhamQuotient
    (d : Module.End R (ExteriorAlgebra R V)) :=
  LinearMap.ker d ⧸ deRhamSubmodule d

/-- The canonical projection from closed forms to de Rham cohomology. -/
def deRhamQuotientMk
    (d : Module.End R (ExteriorAlgebra R V)) :
    LinearMap.ker d → deRhamQuotient d :=
  Submodule.Quotient.mk

theorem continuous_deRhamQuotientMk
    [TopologicalSpace (ExteriorAlgebra R V)]
    (d : Module.End R (ExteriorAlgebra R V)) :
    Continuous (deRhamQuotientMk d) := by
  change Continuous (Submodule.Quotient.mk : LinearMap.ker d →
    LinearMap.ker d ⧸ deRhamSubmodule d)
  exact continuous_quotient_mk'

/-- A continuous map on closed forms descends through the de Rham quotient
when it is invariant under the exact-form quotient relation. -/
theorem continuous_deRhamQuotient_lift
    [TopologicalSpace (ExteriorAlgebra R V)] [TopologicalSpace Y]
    (d : Module.End R (ExteriorAlgebra R V))
    (f : LinearMap.ker d → Y)
    (hf : Continuous f)
    (h_invariant : ∀ a b : LinearMap.ker d,
      (deRhamSubmodule d).quotientRel a b → f a = f b) :
    Continuous (Quotient.lift f h_invariant : deRhamQuotient d → Y) := by
  exact hf.quotient_lift h_invariant

/-- The de Rham quotient as an object of `TopCat`, with its native quotient
topology. -/
def deRhamQuotientTopCat
    [TopologicalSpace (ExteriorAlgebra R V)]
    (d : Module.End R (ExteriorAlgebra R V)) : TopCat :=
  TopCat.of (LinearMap.ker d ⧸ deRhamSubmodule d)

/-- The canonical de Rham projection as a morphism in `TopCat`. -/
def deRhamQuotientMkTopCat
    [TopologicalSpace (ExteriorAlgebra R V)]
    (d : Module.End R (ExteriorAlgebra R V)) :
    TopCat.of (LinearMap.ker d) ⟶ deRhamQuotientTopCat d :=
  TopCat.ofHom
    { toFun := deRhamQuotientMk d
      continuous_toFun := continuous_deRhamQuotientMk d }

end InfoGeometry.Canonical.DeRhamCohomologyQuotientTopologicalBridge

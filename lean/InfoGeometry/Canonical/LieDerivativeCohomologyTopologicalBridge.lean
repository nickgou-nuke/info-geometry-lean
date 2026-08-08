import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.Canonical.DeRhamCohomologyQuotientTopologicalBridge
import InfoGeometry.Canonical.LieDerivativeCohomologyClassZeroBridge
import InfoGeometry.Canonical.CartanLieDerivativeMagicBridge

/-!
# Topological descent of the Lie derivative to de Rham cohomology

The algebraic Lie-derivative owner proves that the Lie derivative of every
closed form is exact.  This companion packages the corresponding map on the
closed-form carrier and invokes the generic quotient-topology descent theorem.
Continuity is an explicit property; it is not inferred from the algebraic
Cartan identities.
-/

noncomputable section

namespace InfoGeometry.Canonical.LieDerivativeCohomologyTopologicalBridge

open ExteriorAlgebra
open CategoryTheory
open InfoGeometry.Canonical.CartanLieDerivativeMagicBridge
open InfoGeometry.Canonical.DeRhamCohomologyQuotientBridge
open InfoGeometry.Canonical.DeRhamCohomologyQuotientTopologicalBridge
open InfoGeometry.Canonical.LieDerivativeCohomologyClassZeroBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Lie derivative restricted to the closed-form carrier. -/
def lieDerivativeClosedMap
    (d iota_X : Module.End R (ExteriorAlgebra R V))
    (hd2 : d.comp d = 0) :
    LinearMap.ker d → LinearMap.ker d :=
  fun w =>
    ⟨lieDerivativeEnd d iota_X w.1, by
      rw [LinearMap.mem_ker]
      have h1 : d (lieDerivativeEnd d iota_X w.1) =
          lieDerivativeEnd d iota_X (d w.1) := by
        have h_comp :=
          LinearMap.congr_fun
            (lieDerivative_commutes_exteriorDerivative_end d iota_X hd2) w.1
        exact h_comp
      rw [h1, w.2, LinearMap.map_zero]⟩

theorem lieDerivativeClosedMap_class_zero
    (d iota_X : Module.End R (ExteriorAlgebra R V))
    (hd2 : d.comp d = 0) (w : LinearMap.ker d) :
    deRhamQuotientMk d (lieDerivativeClosedMap d iota_X hd2 w) =
      deRhamQuotientMk d 0 := by
  simpa [deRhamQuotientMk, lieDerivativeClosedMap] using
    (lie_derivative_cohomology_class_eq_zero d iota_X hd2 w)

theorem continuous_lieDerivativeQuotientMap
    [TopologicalSpace (ExteriorAlgebra R V)]
    (d iota_X : Module.End R (ExteriorAlgebra R V))
    (hd2 : d.comp d = 0)
    (hcont : Continuous (lieDerivativeClosedMap d iota_X hd2)) :
    Continuous
      (deRhamQuotientMap d d (lieDerivativeClosedMap d iota_X hd2) (by
        intro a b _
        rw [lieDerivativeClosedMap_class_zero d iota_X hd2 a,
          lieDerivativeClosedMap_class_zero d iota_X hd2 b])) := by
  exact continuous_deRhamQuotientMap d d
    (lieDerivativeClosedMap d iota_X hd2) hcont (by
    intro a b _
    rw [lieDerivativeClosedMap_class_zero d iota_X hd2 a,
      lieDerivativeClosedMap_class_zero d iota_X hd2 b])

/-- The descended Lie derivative as a continuous endomorphism in `TopCat`. -/
def lieDerivativeQuotientTopCat
    [TopologicalSpace (ExteriorAlgebra R V)]
    (d iota_X : Module.End R (ExteriorAlgebra R V))
    (hd2 : d.comp d = 0)
    (hcont : Continuous (lieDerivativeClosedMap d iota_X hd2)) :
    deRhamQuotientTopCat d ⟶ deRhamQuotientTopCat d :=
  TopCat.ofHom
    { toFun := deRhamQuotientMap d d (lieDerivativeClosedMap d iota_X hd2) (by
        intro a b _
        rw [lieDerivativeClosedMap_class_zero d iota_X hd2 a,
          lieDerivativeClosedMap_class_zero d iota_X hd2 b])
      continuous_toFun := continuous_lieDerivativeQuotientMap d iota_X hd2 hcont }

end InfoGeometry.Canonical.LieDerivativeCohomologyTopologicalBridge

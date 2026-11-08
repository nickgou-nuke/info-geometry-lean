import InfoGeometry.Canonical.CantorProjectiveLimitCategoricalIsoTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CantorProjectiveLimitReadoutTopCat
import InfoGeometry.Canonical.UHFBoundaryInverseLimitReadoutTopCat

/-!
# Readout compatibility across the two prefix-limit presentations

The concrete coherent-family carrier and the categorical `TopCat` limit are
canonically identified through the Cantor boundary.  This owner proves that
their transported binary readouts agree exactly.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorProjectiveLimitInverseLimitReadoutTopCat

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimitCategoricalIsoTopCat
open InfoGeometry.Canonical.CantorProjectiveLimitReadoutTopCat
open InfoGeometry.Canonical.UHFBoundaryInverseLimitReadoutTopCat
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit

theorem projective_inverseLimit_readout_compatibility :
    projectiveToCategoricalLimitTopCatIso.hom ≫
        inverseLimitReadoutTopCatHom =
      projectiveLimitReadoutTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app]
  change realBinaryReadout
      (prefixBoundaryLimitIso.inv
        (projectiveToCategoricalLimitTopCatIso.hom p)) =
    realBinaryReadout (toCantor p)
  have hcarrier :
      prefixBoundaryLimitIso.inv
          (projectiveToCategoricalLimitTopCatIso.hom p) =
        toCantor p := by
    change prefixBoundaryLimitIso.inv
        (prefixBoundaryLimitIso.hom (toCantor p)) = toCantor p
    exact prefixBoundaryLimitIso.hom_inv_id_apply (toCantor p)
  rw [hcarrier]

end InfoGeometry.Canonical.CantorProjectiveLimitInverseLimitReadoutTopCat

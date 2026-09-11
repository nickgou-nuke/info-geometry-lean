import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Transport of morphism equality across the native inverse-limit isomorphism

The compatible-family carrier and the categorical `TopCat` limit are already
identified by an isomorphism.  This owner records the corresponding extensional
principle for maps out of the categorical limit.  It is purely categorical and
does not assert density, KMS, positivity, or a C*-completion theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitTransportExt

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit

theorem inverseLimit_hom_ext_of_compatible_transport
    {Y : Type} [TopologicalSpace Y]
    (g h : limit readoutDiagram ⟶ TopCat.of Y)
    (H : compatibleReadoutInverseLimitIso.hom ≫ g =
      compatibleReadoutInverseLimitIso.hom ≫ h) :
    g = h := by
  exact (cancel_epi compatibleReadoutInverseLimitIso.hom).1 H

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitTransportExt
end

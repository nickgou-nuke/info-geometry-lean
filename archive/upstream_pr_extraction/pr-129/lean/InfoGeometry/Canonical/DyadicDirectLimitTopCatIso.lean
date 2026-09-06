import InfoGeometry.Canonical.DyadicDimensionGroupTopCat

/-!
# The concrete dyadic readout as a `TopCat` isomorphism

The quotient carrier and its transported dyadic topology are not identified
definitionally with the categorical stage colimit.  They are, however,
canonically isomorphic to the dyadic-rational readout object.
-/

namespace InfoGeometry.Canonical.DyadicDirectLimitTopCatIso

open CategoryTheory
open InfoGeometry.Canonical
open InfoGeometry.Canonical.DyadicDimensionGroupTopCat

noncomputable def dyadicDirectLimitTopCatIso :
    dyadicDirectLimitTopCat ≅ dyadicRationalTopCat :=
  TopCat.isoOfHomeo dyadicDirectLimitHomeomorph

theorem dyadicDirectLimitTopCatIso_hom_eq_readout :
    dyadicDirectLimitTopCatIso.hom =
      dyadicDirectLimitReadoutTopCatHom := by
  apply TopCat.hom_ext
  rfl

theorem dyadicDirectLimitTopCatIso_inv_eq_readout :
    dyadicDirectLimitTopCatIso.inv =
      dyadicDirectLimitReadoutInverseTopCatHom := by
  apply TopCat.hom_ext
  rfl

end InfoGeometry.Canonical.DyadicDirectLimitTopCatIso

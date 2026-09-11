import InfoGeometry.Canonical.DyadicDirectLimitTopology
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.DyadicDimensionGroupTopCat

open CategoryTheory

noncomputable section

def dyadicDirectLimitTopCat : TopCat :=
  TopCat.of DyadicDirectLimit

def dyadicRationalTopCat : TopCat :=
  TopCat.of DyadicRational

noncomputable def dyadicDirectLimitReadoutTopCatHom :
    dyadicDirectLimitTopCat ⟶ dyadicRationalTopCat :=
  TopCat.ofHom
    { toFun := dyadicDirectLimitEquiv
      continuous_toFun := continuous_dyadicDirectLimitEquiv }

noncomputable def dyadicDirectLimitReadoutInverseTopCatHom :
    dyadicRationalTopCat ⟶ dyadicDirectLimitTopCat :=
  TopCat.ofHom
    { toFun := dyadicDirectLimitEquiv.symm
      continuous_toFun := continuous_dyadicDirectLimitEquiv_symm }

theorem dyadicDirectLimitReadoutTopCatHom_comp_inverse :
    dyadicDirectLimitReadoutTopCatHom ≫
        dyadicDirectLimitReadoutInverseTopCatHom =
      𝟙 dyadicDirectLimitTopCat := by
  apply TopCat.hom_ext
  ext x
  exact dyadicDirectLimitEquiv.symm_apply_apply x

theorem dyadicDirectLimitReadoutInverseTopCatHom_comp :
    dyadicDirectLimitReadoutInverseTopCatHom ≫
        dyadicDirectLimitReadoutTopCatHom =
      𝟙 dyadicRationalTopCat := by
  apply TopCat.hom_ext
  ext q
  exact dyadicDirectLimitEquiv.apply_symm_apply q

theorem dyadicDirectLimitReadoutTopCatHom_isIso :
    IsIso dyadicDirectLimitReadoutTopCatHom := by
  refine IsIso.mk ⟨dyadicDirectLimitReadoutInverseTopCatHom, ?_, ?_⟩
  · exact dyadicDirectLimitReadoutTopCatHom_comp_inverse
  · exact dyadicDirectLimitReadoutInverseTopCatHom_comp

end
end InfoGeometry.Canonical.DyadicDimensionGroupTopCat

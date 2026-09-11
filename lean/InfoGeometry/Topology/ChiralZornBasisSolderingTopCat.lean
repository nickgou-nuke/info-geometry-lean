import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.ChiralZornBasisSolderingTopological

/-!
# TopCat presentation of the chiral/soldered coordinate change

The preceding owner proves the coordinate change is a homeomorphism.  This
file only presents that existing homeomorphism as an isomorphism in `TopCat`.
-/

namespace InfoGeometry.Topology

open CategoryTheory

noncomputable section

def chiralToSolderedTopCatHom :
    TopCat.of ChiralCoefficientSpace ⟶ TopCat.of ChiralCoefficientSpace :=
  TopCat.ofHom
    { toFun := chiralToSoldered
      continuous_toFun := continuous_chiralToSoldered }

def solderedToChiralTopCatHom :
    TopCat.of ChiralCoefficientSpace ⟶ TopCat.of ChiralCoefficientSpace :=
  TopCat.ofHom
    { toFun := chiralToSoldered.symm
      continuous_toFun := continuous_solderedToChiral }

theorem chiralToSolderedTopCatHom_apply (c : ChiralCoefficientSpace) :
    chiralToSolderedTopCatHom c = chiralToSoldered c := rfl

theorem solderedToChiralTopCatHom_apply (c : ChiralCoefficientSpace) :
    solderedToChiralTopCatHom c = chiralToSoldered.symm c := rfl

theorem chiralToSolderedTopCatHom_comp_inverse :
    chiralToSolderedTopCatHom ≫ solderedToChiralTopCatHom =
      𝟙 (TopCat.of ChiralCoefficientSpace) := by
  ext c i
  exact congrFun (chiralToSoldered.left_inv c) i

theorem solderedToChiralTopCatHom_comp_forward :
    solderedToChiralTopCatHom ≫ chiralToSolderedTopCatHom =
      𝟙 (TopCat.of ChiralCoefficientSpace) := by
  ext c i
  exact congrFun (chiralToSoldered.right_inv c) i

theorem chiralToSolderedTopCatHom_isIso :
    IsIso chiralToSolderedTopCatHom := by
  refine IsIso.mk ⟨solderedToChiralTopCatHom, ?_, ?_⟩
  · exact chiralToSolderedTopCatHom_comp_inverse
  · exact solderedToChiralTopCatHom_comp_forward

theorem solderedToChiralTopCatHom_isIso :
    IsIso solderedToChiralTopCatHom := by
  refine IsIso.mk ⟨chiralToSolderedTopCatHom, ?_, ?_⟩
  · exact solderedToChiralTopCatHom_comp_forward
  · exact chiralToSolderedTopCatHom_comp_inverse

end
end InfoGeometry.Topology

import InfoGeometry.Topology.NaryTreeBoundaryQuotientHomeomorphAction
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff quotient actions of the boundary

This owner packages the native quotient action in `CompHaus`.  The quotient
map and the descended action are related by an actual naturality equality;
the quotient action is not introduced as an abstract categorical property.
-/

noncomputable section

namespace InfoGeometry.Topology.NaryTreeBoundaryQuotientCompHausAction

open CategoryTheory
open InfoGeometry.Topology.NaryTreeBoundaryQuotientHomeomorphAction

variable {A : Type} [TopologicalSpace A] [CompactSpace A] [T2Space A]

noncomputable def boundaryCoordinatewiseCompHausIso
    (a : NaryTreeBoundaryInverseLimit.Boundary (A := A) ≃ₜ
      NaryTreeBoundaryInverseLimit.Boundary (A := A)) :
    CompHaus.of (NaryTreeBoundaryInverseLimit.Boundary (A := A)) ≅
      CompHaus.of (NaryTreeBoundaryInverseLimit.Boundary (A := A)) :=
  { hom := ⟨TopCat.ofHom
        { toFun := a
          continuous_toFun := a.continuous_toFun }⟩
    inv := ⟨TopCat.ofHom
        { toFun := a.symm
          continuous_toFun := a.symm.continuous_toFun }⟩
    hom_inv_id := by
      apply ConcreteCategory.hom_ext
      intro x
      change a.symm (a x) = x
      exact a.symm_apply_apply x
    inv_hom_id := by
      apply ConcreteCategory.hom_ext
      intro x
      change a (a.symm x) = x
      exact a.apply_symm_apply x }

noncomputable def boundaryQuotientCompHausHom
    (r : Setoid (NaryTreeBoundaryInverseLimit.Boundary (A := A)))
    [CompactSpace (NaryTreeBoundaryQuotientTopCat.BoundaryQuotient (A := A) r)]
    [T2Space (NaryTreeBoundaryQuotientTopCat.BoundaryQuotient (A := A) r)] :
    CompHaus.of (NaryTreeBoundaryInverseLimit.Boundary (A := A)) ⟶
      CompHaus.of (NaryTreeBoundaryQuotientTopCat.BoundaryQuotient (A := A) r) :=
  ⟨NaryTreeBoundaryQuotientTopCat.boundaryQuotientTopCatHom (A := A) r⟩

noncomputable def quotientActionCompHausIso
    (r : Setoid (NaryTreeBoundaryInverseLimit.Boundary (A := A)))
    (a : NaryTreeBoundaryInverseLimit.Boundary (A := A) ≃ₜ
      NaryTreeBoundaryInverseLimit.Boundary (A := A))
    (hrel : ∀ ⦃x y : NaryTreeBoundaryInverseLimit.Boundary (A := A)⦄,
      r.r x y → r.r (a x) (a y))
    (hrel_symm : ∀ ⦃x y : NaryTreeBoundaryInverseLimit.Boundary (A := A)⦄,
      r.r x y → r.r (a.symm x) (a.symm y))
    [CompactSpace (NaryTreeBoundaryQuotientTopCat.BoundaryQuotient (A := A) r)]
    [T2Space (NaryTreeBoundaryQuotientTopCat.BoundaryQuotient (A := A) r)] :
    CompHaus.of (NaryTreeBoundaryQuotientTopCat.BoundaryQuotient (A := A) r) ≅
      CompHaus.of (NaryTreeBoundaryQuotientTopCat.BoundaryQuotient (A := A) r) := by
  let h := quotientActionHomeomorph r a hrel hrel_symm
  exact
    { hom := ⟨TopCat.ofHom
          { toFun := h
            continuous_toFun := h.continuous_toFun }⟩
      inv := ⟨TopCat.ofHom
          { toFun := h.symm
            continuous_toFun := h.symm.continuous_toFun }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro x
        change h.symm (h x) = x
        exact h.symm_apply_apply x
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro x
        change h (h.symm x) = x
        exact h.apply_symm_apply x }

theorem boundaryQuotientCompHausHom_natural
    (r : Setoid (NaryTreeBoundaryInverseLimit.Boundary (A := A)))
    (a : NaryTreeBoundaryInverseLimit.Boundary (A := A) ≃ₜ
      NaryTreeBoundaryInverseLimit.Boundary (A := A))
    (hrel : ∀ ⦃x y : NaryTreeBoundaryInverseLimit.Boundary (A := A)⦄,
      r.r x y → r.r (a x) (a y))
    (hrel_symm : ∀ ⦃x y : NaryTreeBoundaryInverseLimit.Boundary (A := A)⦄,
      r.r x y → r.r (a.symm x) (a.symm y))
    [CompactSpace (NaryTreeBoundaryQuotientTopCat.BoundaryQuotient (A := A) r)]
    [T2Space (NaryTreeBoundaryQuotientTopCat.BoundaryQuotient (A := A) r)] :
    boundaryQuotientCompHausHom (A := A) r ≫
        (quotientActionCompHausIso (A := A) r a hrel hrel_symm).hom =
      (boundaryCoordinatewiseCompHausIso (A := A) a).hom ≫
        boundaryQuotientCompHausHom (A := A) r := by
  apply ConcreteCategory.hom_ext
  intro x
  simp only [CategoryTheory.comp_apply]
  change quotientAction r a hrel
      (NaryTreeBoundaryQuotientTopCat.boundaryQuotientMap (A := A) r x) =
    NaryTreeBoundaryQuotientTopCat.boundaryQuotientMap (A := A) r (a x)
  exact quotientAction_mk r a hrel x

end InfoGeometry.Topology.NaryTreeBoundaryQuotientCompHausAction

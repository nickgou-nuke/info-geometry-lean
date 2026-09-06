import InfoGeometry.Topology.NaryTreeBoundaryQuotientTopCat

/-!
# Quotient transport of boundary homeomorphisms

A homeomorphism of the native boundary descends to the quotient whenever it
preserves the quotient relation, and its inverse preserves the relation as
well.  This is the genuine topological action layer above the quotient map.
-/

noncomputable section

namespace InfoGeometry.Topology.NaryTreeBoundaryQuotientHomeomorphAction

open InfoGeometry.Topology.NaryTreeBoundaryInverseLimit

variable {A : Type} [TopologicalSpace A]

def quotientAction
    (r : Setoid (Boundary (A := A)))
    (a : Boundary (A := A) ≃ₜ Boundary (A := A))
    (hrel : ∀ ⦃x y : Boundary (A := A)⦄,
      r.r x y → r.r (a x) (a y)) :
    NaryTreeBoundaryQuotientTopCat.BoundaryQuotient (A := A) r →
      NaryTreeBoundaryQuotientTopCat.BoundaryQuotient (A := A) r :=
  NaryTreeBoundaryQuotientTopCat.quotientReadout (A := A) r
    (fun x => NaryTreeBoundaryQuotientTopCat.boundaryQuotientMap (A := A) r (a x))
    (by
      intro x y h
      exact Quotient.sound (hrel h))

@[simp] theorem quotientAction_mk
    (r : Setoid (Boundary (A := A)))
    (a : Boundary (A := A) ≃ₜ Boundary (A := A))
    (hrel : ∀ ⦃x y : Boundary (A := A)⦄,
      r.r x y → r.r (a x) (a y))
    (x : Boundary (A := A)) :
    quotientAction r a hrel
        (NaryTreeBoundaryQuotientTopCat.boundaryQuotientMap (A := A) r x) =
      NaryTreeBoundaryQuotientTopCat.boundaryQuotientMap (A := A) r (a x) := by
  rfl

theorem continuous_quotientAction
    (r : Setoid (Boundary (A := A)))
    (a : Boundary (A := A) ≃ₜ Boundary (A := A))
    (hrel : ∀ ⦃x y : Boundary (A := A)⦄,
      r.r x y → r.r (a x) (a y)) :
    Continuous (quotientAction r a hrel) := by
  apply NaryTreeBoundaryQuotientTopCat.continuous_quotientReadout
  exact (NaryTreeBoundaryQuotientTopCat.continuous_boundaryQuotientMap
    (A := A) r).comp a.continuous

noncomputable def quotientActionHomeomorph
    (r : Setoid (Boundary (A := A)))
    (a : Boundary (A := A) ≃ₜ Boundary (A := A))
    (hrel : ∀ ⦃x y : Boundary (A := A)⦄,
      r.r x y → r.r (a x) (a y))
    (hrel_symm : ∀ ⦃x y : Boundary (A := A)⦄,
      r.r x y → r.r (a.symm x) (a.symm y)) :
    NaryTreeBoundaryQuotientTopCat.BoundaryQuotient (A := A) r ≃ₜ
      NaryTreeBoundaryQuotientTopCat.BoundaryQuotient (A := A) r where
  toEquiv :=
    { toFun := quotientAction r a hrel
      invFun := quotientAction r a.symm hrel_symm
      left_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro x
        change quotientAction r a.symm hrel_symm
            (NaryTreeBoundaryQuotientTopCat.boundaryQuotientMap (A := A) r (a x)) =
          NaryTreeBoundaryQuotientTopCat.boundaryQuotientMap (A := A) r x
        rw [quotientAction_mk]
        congr 1
        exact a.symm_apply_apply x
      right_inv := by
        intro q
        refine Quotient.inductionOn q ?_
        intro x
        change quotientAction r a hrel
            (NaryTreeBoundaryQuotientTopCat.boundaryQuotientMap (A := A) r (a.symm x)) =
          NaryTreeBoundaryQuotientTopCat.boundaryQuotientMap (A := A) r x
        rw [quotientAction_mk]
        congr 1
        exact a.apply_symm_apply x }
  continuous_toFun := continuous_quotientAction r a hrel
  continuous_invFun := continuous_quotientAction r a.symm hrel_symm

@[simp] theorem quotientActionHomeomorph_apply_mk
    (r : Setoid (Boundary (A := A)))
    (a : Boundary (A := A) ≃ₜ Boundary (A := A))
    (hrel : ∀ ⦃x y : Boundary (A := A)⦄,
      r.r x y → r.r (a x) (a y))
    (hrel_symm : ∀ ⦃x y : Boundary (A := A)⦄,
      r.r x y → r.r (a.symm x) (a.symm y))
    (x : Boundary (A := A)) :
    quotientActionHomeomorph r a hrel hrel_symm
        (NaryTreeBoundaryQuotientTopCat.boundaryQuotientMap (A := A) r x) =
      NaryTreeBoundaryQuotientTopCat.boundaryQuotientMap (A := A) r (a x) := by
  rfl

end InfoGeometry.Topology.NaryTreeBoundaryQuotientHomeomorphAction

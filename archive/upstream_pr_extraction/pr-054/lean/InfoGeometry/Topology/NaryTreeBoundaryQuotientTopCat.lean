import InfoGeometry.Topology.NaryTreeBoundaryInverseLimit

/-!
# Explicit quotients of an n-ary tree boundary

This owner packages the native quotient topology for an explicit `Setoid` on
the boundary.  It proves the quotient map and the universal factorization of
continuous relation-invariant readouts.  No target space, interval, or
endpoint-identification theorem is assumed.
-/

noncomputable section

namespace InfoGeometry.Topology.NaryTreeBoundaryQuotientTopCat

open TopologicalSpace
open CategoryTheory

variable {A : Type} [TopologicalSpace A]

abbrev Boundary :=
  NaryTreeBoundaryInverseLimit.Boundary (A := A)

abbrev BoundaryQuotient (r : Setoid (Boundary (A := A))) :=
  Quotient r

def boundaryQuotientMap
    (r : Setoid (Boundary (A := A))) :
    Boundary (A := A) → BoundaryQuotient r :=
  Quotient.mk' (s := r)

theorem continuous_boundaryQuotientMap
    (r : Setoid (Boundary (A := A))) :
    Continuous (boundaryQuotientMap (A := A) r) := by
  exact continuous_quotient_mk'

theorem isQuotientMap_boundaryQuotientMap
    (r : Setoid (Boundary (A := A))) :
    Topology.IsQuotientMap (boundaryQuotientMap (A := A) r) := by
  exact isQuotientMap_quotient_mk'

/-! A compact-to-Hausdorff continuous surjection is already a quotient map in
Mathlib.  This is the general topological bridge used by concrete readouts;
the identification of a particular quotient with an interval remains a
separate theorem. -/
theorem isQuotientMap_of_compactSpace_of_t2
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y]
    (f : X → Y) (h_surj : Function.Surjective f)
    (h_cont : Continuous f) :
    Topology.IsQuotientMap f := by
  exact IsQuotientMap.of_surjective_continuous h_surj h_cont

def boundaryQuotientTopCatHom
    (r : Setoid (Boundary (A := A))) :
    TopCat.of (Boundary (A := A)) ⟶
      TopCat.of (BoundaryQuotient r) :=
  TopCat.ofHom
    { toFun := boundaryQuotientMap (A := A) r
      continuous_toFun := continuous_boundaryQuotientMap (A := A) r }

def quotientReadout
    {Y : Type} [TopologicalSpace Y]
    (r : Setoid (Boundary (A := A)))
    (f : Boundary (A := A) → Y)
    (hinv : ∀ ⦃x y : Boundary (A := A)⦄,
      r.r x y → f x = f y) :
    BoundaryQuotient r → Y :=
  Quotient.lift (s := r) f (by
    intro x y h
    exact hinv h)

theorem quotientReadout_mk
    {Y : Type} [TopologicalSpace Y]
    (r : Setoid (Boundary (A := A)))
    (f : Boundary (A := A) → Y)
    (hinv : ∀ ⦃x y : Boundary (A := A)⦄,
      r.r x y → f x = f y)
    (x : Boundary (A := A)) :
    quotientReadout (A := A) r f hinv
      (boundaryQuotientMap (A := A) r x) = f x := by
  rfl

theorem continuous_quotientReadout
    {Y : Type} [TopologicalSpace Y]
    (r : Setoid (Boundary (A := A)))
    (f : Boundary (A := A) → Y)
    (hf : Continuous f)
    (hinv : ∀ ⦃x y : Boundary (A := A)⦄,
      r.r x y → f x = f y) :
    Continuous (quotientReadout (A := A) r f hinv) := by
  exact Continuous.quotient_lift hf (by
    intro x y h
    exact hinv h)

def quotientReadoutTopCatHom
    {Y : Type} [TopologicalSpace Y]
    (r : Setoid (Boundary (A := A)))
    (f : Boundary (A := A) → Y)
    (hf : Continuous f)
    (hinv : ∀ ⦃x y : Boundary (A := A)⦄,
      r.r x y → f x = f y) :
    TopCat.of (BoundaryQuotient r) ⟶ TopCat.of Y :=
  TopCat.ofHom
    { toFun := quotientReadout (A := A) r f hinv
      continuous_toFun := continuous_quotientReadout
        (A := A) r f hf hinv }

theorem boundaryQuotientTopCatHom_factorization
    {Y : Type} [TopologicalSpace Y]
    (r : Setoid (Boundary (A := A)))
    (f : Boundary (A := A) → Y)
    (hf : Continuous f)
    (hinv : ∀ ⦃x y : Boundary (A := A)⦄,
      r.r x y → f x = f y) :
    boundaryQuotientTopCatHom (A := A) r ≫
        quotientReadoutTopCatHom (A := A) r f hf hinv =
      TopCat.ofHom
        { toFun := f
          continuous_toFun := hf } := by
  apply TopCat.hom_ext
  ext x
  rfl

end InfoGeometry.Topology.NaryTreeBoundaryQuotientTopCat

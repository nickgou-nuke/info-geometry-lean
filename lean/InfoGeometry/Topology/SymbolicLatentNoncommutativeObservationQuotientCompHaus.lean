import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationTopCat
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff packaging of noncommutative observational quotients

For a compact latent carrier, the quotient by equality of operator-valued
observations is canonically homeomorphic to the compact range of the
operator-valued readout.  The algebra target remains `(ι → A)`; this owner
does not replace it by scalar coordinates.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X]
  [NormedRing A] [Fintype ι]

theorem injective_operatorObservationQuotientReadout
    (S : NoncommutativeObservableSystem X A ι) :
    Function.Injective (operatorObservationQuotientReadout S) := by
  intro a
  refine Quotient.inductionOn a ?_
  intro x b
  refine Quotient.inductionOn b ?_
  intro y h
  apply Quotient.sound
  change S.operatorObservationMap x = S.operatorObservationMap y at h
  exact h

noncomputable def operatorObservationQuotientRangeMap
    (S : NoncommutativeObservableSystem X A ι) :
    OperatorObservationalQuotient S →
      Set.range S.operatorObservationMap :=
  Quotient.lift (s := operatorObservationalSetoid S)
    (fun x => ⟨S.operatorObservationMap x, ⟨x, rfl⟩⟩)
    (by
      intro x y h
      apply Subtype.ext
      exact h)

@[simp] theorem operatorObservationQuotientRangeMap_apply
    (S : NoncommutativeObservableSystem X A ι) (x : X) :
    operatorObservationQuotientRangeMap S
        (operatorObservationQuotientMap S x) =
      ⟨S.operatorObservationMap x, ⟨x, rfl⟩⟩ := by
  rfl

theorem operatorObservationQuotientRangeMap_val
    (S : NoncommutativeObservableSystem X A ι)
    (q : OperatorObservationalQuotient S) :
    (operatorObservationQuotientRangeMap S q).1 =
      operatorObservationQuotientReadout S q := by
  refine Quotient.inductionOn q ?_
  intro x
  rfl

noncomputable def operatorObservationQuotientRangeEquiv
    (S : NoncommutativeObservableSystem X A ι) :
    OperatorObservationalQuotient S ≃
      Set.range S.operatorObservationMap :=
  Equiv.ofBijective (operatorObservationQuotientRangeMap S) (by
    constructor
    · intro a b h
      have hval := congrArg Subtype.val h
      apply injective_operatorObservationQuotientReadout S
      rw [← operatorObservationQuotientRangeMap_val S a,
        ← operatorObservationQuotientRangeMap_val S b]
      exact hval
    · intro y
      rcases y with ⟨z, ⟨x, hx⟩⟩
      refine ⟨operatorObservationQuotientMap S x, ?_⟩
      apply Subtype.ext
      simpa [operatorObservationQuotientRangeMap_apply] using hx)

theorem continuous_operatorObservationQuotientRangeMap
    (S : NoncommutativeObservableSystem X A ι) :
    Continuous (operatorObservationQuotientRangeMap S) := by
  apply continuous_induced_rng.mpr
  simpa [Function.comp_def, operatorObservationQuotientRangeMap_val] using
    continuous_operatorObservationQuotientReadout S

theorem operatorObservationQuotientRangeMap_isQuotientMap
    (S : NoncommutativeObservableSystem X A ι) :
    Topology.IsQuotientMap (operatorObservationQuotientRangeMap S) := by
  exact IsQuotientMap.of_surjective_continuous
    (operatorObservationQuotientRangeEquiv S).surjective
    (continuous_operatorObservationQuotientRangeMap S)

noncomputable def operatorObservationQuotientRangeHomeomorph
    (S : NoncommutativeObservableSystem X A ι) :
    OperatorObservationalQuotient S ≃ₜ
      Set.range S.operatorObservationMap := by
  let hquot := operatorObservationQuotientRangeMap_isQuotientMap S
  refine
    { toEquiv := operatorObservationQuotientRangeEquiv S
      continuous_toFun := continuous_operatorObservationQuotientRangeMap S
      continuous_invFun := ?_ }
  apply hquot.continuous_iff.mpr
  change Continuous ((operatorObservationQuotientRangeEquiv S).symm ∘
    operatorObservationQuotientRangeMap S)
  have hcomp :
      (operatorObservationQuotientRangeEquiv S).symm ∘
          operatorObservationQuotientRangeMap S = id := by
    funext q
    exact (operatorObservationQuotientRangeEquiv S).left_inv q
  rw [hcomp]
  exact continuous_id

noncomputable def operatorObservationRangeCompHaus
    (S : NoncommutativeObservableSystem X A ι) : CompHaus := by
  letI : CompactSpace (Set.range S.operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap S))
  exact CompHaus.of (Set.range S.operatorObservationMap)

noncomputable def operatorObservationQuotientCompHaus
    (S : NoncommutativeObservableSystem X A ι) : CompHaus := by
  letI : CompactSpace (Set.range S.operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap S))
  letI : CompactSpace (OperatorObservationalQuotient S) :=
    (operatorObservationQuotientRangeHomeomorph S).symm.compactSpace
  letI : T2Space (OperatorObservationalQuotient S) :=
    (operatorObservationQuotientRangeHomeomorph S).symm.t2Space
  exact CompHaus.of (OperatorObservationalQuotient S)

noncomputable def operatorObservationQuotientCompHausIso
    (S : NoncommutativeObservableSystem X A ι) :
    operatorObservationQuotientCompHaus S ≅
      operatorObservationRangeCompHaus S := by
  letI : CompactSpace (Set.range S.operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap S))
  letI : CompactSpace (OperatorObservationalQuotient S) :=
    (operatorObservationQuotientRangeHomeomorph S).symm.compactSpace
  letI : T2Space (OperatorObservationalQuotient S) :=
    (operatorObservationQuotientRangeHomeomorph S).symm.t2Space
  let e := operatorObservationQuotientRangeHomeomorph S
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := e
          continuous_toFun := e.continuous_toFun }⟩
      inv := ⟨TopCat.ofHom
        { toFun := e.symm
          continuous_toFun := e.symm.continuous_toFun }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro q
        change e.symm (e q) = q
        exact e.symm_apply_apply q
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e (e.symm y) = y
        exact e.apply_symm_apply y }

@[simp] theorem operatorObservationQuotientCompHausIso_hom_apply
    (S : NoncommutativeObservableSystem X A ι)
    (q : OperatorObservationalQuotient S) :
    (operatorObservationQuotientCompHausIso S).hom q =
      operatorObservationQuotientRangeMap S q := by
  rfl

end InfoGeometry.Topology

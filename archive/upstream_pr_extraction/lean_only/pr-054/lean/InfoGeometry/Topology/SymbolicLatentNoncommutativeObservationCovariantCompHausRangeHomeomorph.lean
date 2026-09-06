import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationCovariantCompHausRangeActionLaws
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Homeomorphism and `CompHaus` isomorphism for the operator-observation range

When the covariant operator action is continuous at both `t` and `-t`, the
range action is a concrete homeomorphism.  This owner packages the same fact
both as a `Homeomorph` and as an isomorphism in `CompHaus`.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

noncomputable def operatorObservationRangeCovariantFlowHomeomorph
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (h_t : Continuous (Φ.operatorAction t))
    (h_neg_t : Continuous (Φ.operatorAction (-t))) :
    Set.range S.operatorObservationMap ≃ₜ Set.range S.operatorObservationMap := by
  letI : CompactSpace (Set.range S.operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap S))
  let f := operatorObservationRangeCompHausCovariantFlowHom Φ t h_t
  let g := operatorObservationRangeCompHausCovariantFlowHom Φ (-t) h_neg_t
  exact
    { toEquiv :=
        { toFun := f
          invFun := g
          left_inv := by
            intro y
            apply Subtype.ext
            funext i
            change Φ.operatorAction (-t) (Φ.operatorAction t (y.1 i)) = y.1 i
            calc
              Φ.operatorAction (-t) (Φ.operatorAction t (y.1 i)) =
                  Φ.operatorAction (-t + t) (y.1 i) :=
                (Φ.operatorAction_add (-t) t _).symm
              _ = y.1 i := by
                rw [neg_add_cancel]
                exact Φ.operatorAction_zero _
          right_inv := by
            intro y
            apply Subtype.ext
            funext i
            change Φ.operatorAction t (Φ.operatorAction (-t) (y.1 i)) = y.1 i
            calc
              Φ.operatorAction t (Φ.operatorAction (-t) (y.1 i)) =
                  Φ.operatorAction (t + -t) (y.1 i) :=
                (Φ.operatorAction_add t (-t) _).symm
              _ = y.1 i := by
                rw [add_neg_cancel]
                exact Φ.operatorAction_zero _ }
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_pi (fun i =>
          h_t.comp ((continuous_apply i).comp continuous_subtype_val))
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_pi (fun i =>
          h_neg_t.comp ((continuous_apply i).comp continuous_subtype_val)) }

@[simp] theorem operatorObservationRangeCovariantFlowHomeomorph_apply
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (h_t : Continuous (Φ.operatorAction t))
    (h_neg_t : Continuous (Φ.operatorAction (-t)))
    (y : Set.range S.operatorObservationMap) :
    operatorObservationRangeCovariantFlowHomeomorph Φ t h_t h_neg_t y =
      operatorObservationRangeCompHausCovariantFlowHom Φ t h_t y := by
  rfl

noncomputable def operatorObservationRangeCovariantFlowCompHausIso
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (h_t : Continuous (Φ.operatorAction t))
    (h_neg_t : Continuous (Φ.operatorAction (-t))) :
    operatorObservationRangeCompHaus S ≅ operatorObservationRangeCompHaus S :=
  letI : CompactSpace (Set.range S.operatorObservationMap) :=
    isCompact_iff_compactSpace.mp
      (isCompact_range (continuous_operatorObservationMap S))
  let e := operatorObservationRangeCovariantFlowHomeomorph Φ t h_t h_neg_t
  { hom := ⟨TopCat.ofHom
      { toFun := e
        continuous_toFun := e.continuous_toFun }⟩
    inv := ⟨TopCat.ofHom
      { toFun := e.symm
        continuous_toFun := e.symm.continuous_toFun }⟩
    hom_inv_id := by
      apply ConcreteCategory.hom_ext
      intro y
      change e.symm (e y) = y
      exact e.symm_apply_apply y
    inv_hom_id := by
      apply ConcreteCategory.hom_ext
      intro y
      change e (e.symm y) = y
      exact e.apply_symm_apply y }

@[simp] theorem operatorObservationRangeCovariantFlowCompHausIso_hom_apply
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (h_t : Continuous (Φ.operatorAction t))
    (h_neg_t : Continuous (Φ.operatorAction (-t)))
    (y : operatorObservationRangeCompHaus S) :
    (operatorObservationRangeCovariantFlowCompHausIso Φ t h_t h_neg_t).hom y =
      operatorObservationRangeCompHausCovariantFlowHom Φ t h_t y := by
  change operatorObservationRangeCovariantFlowHomeomorph Φ t h_t h_neg_t y =
    operatorObservationRangeCompHausCovariantFlowHom Φ t h_t y
  rw [operatorObservationRangeCovariantFlowHomeomorph_apply]

end InfoGeometry.Topology

end

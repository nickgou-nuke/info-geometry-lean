import InfoGeometry.Topology.SymbolicLatentNoncommutativeObservationCovariantCompHausFlow

/-!
# Inverse-time homeomorphisms for covariant compact flows

The `StarAlgEquiv` acts on the operator-valued observations.  This owner
packages only the induced real topological homeomorphism of the compact
commuting locus.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

universe u

variable {X A ι : Type u}
  [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedRing A] [StarRing A] [Algebra ℂ A] [Fintype ι]

noncomputable def operatorCommutingLocusCovariantFlowHomeomorph
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) :
    {x : X // x ∈ operatorCommutingLocus S} ≃ₜ
      {x : X // x ∈ operatorCommutingLocus S} where
  toFun := fun x =>
    ⟨Φ.act t x.1,
      (operatorCommutingLocus_covariant_iff Φ t x.1).2 x.2⟩
  invFun := fun x =>
    ⟨Φ.act (-t) x.1,
      (operatorCommutingLocus_covariant_iff Φ (-t) x.1).2 x.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    calc
      Φ.act (-t) (Φ.act t x.1) = Φ.act (-t + t) x.1 := by
        exact (Φ.act_add (-t) t x.1).symm
      _ = x.1 := by rw [neg_add_cancel, Φ.act_zero]
  right_inv := by
    intro x
    apply Subtype.ext
    calc
      Φ.act t (Φ.act (-t) x.1) = Φ.act (t + -t) x.1 := by
        exact (Φ.act_add t (-t) x.1).symm
      _ = x.1 := by rw [add_neg_cancel, Φ.act_zero]
  continuous_toFun :=
    (Φ.continuous_act.comp
      (continuous_const.prodMk continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    (Φ.continuous_act.comp
      (continuous_const.prodMk continuous_subtype_val)).subtype_mk _

@[simp] theorem operatorCommutingLocusCovariantFlowHomeomorph_apply
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ)
    (x : {x : X // x ∈ operatorCommutingLocus S}) :
    operatorCommutingLocusCovariantFlowHomeomorph Φ t x =
      ⟨Φ.act t x.1,
        (operatorCommutingLocus_covariant_iff Φ t x.1).2 x.2⟩ := rfl

noncomputable def operatorCommutingLocusCovariantFlowIso
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) :
    operatorCommutingLocusCompHaus S ≅
      operatorCommutingLocusCompHaus S := by
  letI : CompactSpace {x : X // x ∈ operatorCommutingLocus S} :=
    isCompact_iff_compactSpace.mp (isCompact_operatorCommutingLocus S)
  let e := operatorCommutingLocusCovariantFlowHomeomorph Φ t
  exact
    { hom := ⟨TopCat.ofHom
        { toFun := e
          continuous_toFun := e.continuous_toFun }⟩
      inv := ⟨TopCat.ofHom
        { toFun := e.symm
          continuous_toFun := e.symm.continuous_toFun }⟩
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro x
        change e.symm (e x) = x
        exact e.symm_apply_apply x
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro y
        change e (e.symm y) = y
        exact e.apply_symm_apply y }

theorem operatorCommutingLocusCovariantFlowIso_hom_eq_flowHom
    {S : NoncommutativeObservableSystem X A ι}
    (Φ : NoncommutativeObservableCovariantFlow S) (t : ℝ) :
    (operatorCommutingLocusCovariantFlowIso Φ t).hom =
      operatorCommutingLocusCompHausCovariantFlowHom Φ t := by
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end InfoGeometry.Topology

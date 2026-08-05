import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureCompHaus
import InfoGeometry.Topology.SymbolicLatentModularOrbitClosureFlowTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff modular transport of orbit closures

The `TopCat` owner already constructs the flow map between closed orbit
closures.  This file lifts that map to `CompHaus` using the native compact
subtypes, and records the faithful-forgetful compatibility.  No additional
compactness, recurrence, or minimality assertion is introduced.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]

noncomputable def SymbolicLatentModularFlow.orbitClosureFlowCompHausHom
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ) :
    symbolicLatentModularOrbitClosureCompHaus Φ x ⟶
      symbolicLatentModularOrbitClosureCompHaus Φ (Φ.act t x) := by
  letI : CompactSpace (SymbolicLatentModularOrbitClosure Φ x) :=
    isCompact_iff_compactSpace.mp (Φ.isCompact_orbitClosure x)
  letI : CompactSpace (SymbolicLatentModularOrbitClosure Φ (Φ.act t x)) :=
    isCompact_iff_compactSpace.mp (Φ.isCompact_orbitClosure (Φ.act t x))
  change CompHaus.of (SymbolicLatentModularOrbitClosure Φ x) ⟶
    CompHaus.of (SymbolicLatentModularOrbitClosure Φ (Φ.act t x))
  exact ⟨Φ.orbitClosureFlowTopCatHom t x⟩

theorem SymbolicLatentModularFlow.orbitClosureFlowCompHausHom_forget
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ) :
    compHausToTop.map (Φ.orbitClosureFlowCompHausHom x t) =
      Φ.orbitClosureFlowTopCatHom t x := by
  rfl

@[simp] theorem SymbolicLatentModularFlow.orbitClosureFlowCompHausHom_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ)
    (y : SymbolicLatentModularOrbitClosure Φ x) :
    Φ.orbitClosureFlowCompHausHom x t y =
      ⟨Φ.act t y.1, by
        rw [← Φ.actHomeomorph_image_orbitClosure t x]
        exact ⟨y.1, y.2, rfl⟩⟩ := by
  rfl

theorem SymbolicLatentModularFlow.orbitClosureFlowCompHausHom_natural
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ) :
    compHausToTop.map (Φ.orbitClosureFlowCompHausHom x t) ≫
        Φ.orbitClosureInclusionTopCatHom (Φ.act t x) =
      Φ.orbitClosureInclusionTopCatHom x ≫ Φ.actTopCatHom t := by
  rw [Φ.orbitClosureFlowCompHausHom_forget]
  exact Φ.orbitClosureFlowTopCatHom_natural t x

theorem SymbolicLatentModularFlow.orbitClosureFlowCompHausHom_comp_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) (t s : ℝ)
    (y : symbolicLatentModularOrbitClosureCompHaus Φ x) :
    (((Φ.orbitClosureFlowCompHausHom x t ≫
        Φ.orbitClosureFlowCompHausHom (Φ.act t x) s) y).1) =
      (Φ.orbitClosureFlowCompHausHom x (t + s) y).1 := by
  change Φ.act s (Φ.act t y.1) = Φ.act (t + s) y.1
  simpa [add_comm] using (Φ.add_apply s t y.1).symm

/-! A time slice restricts to a homeomorphism between the two native closed
orbit subspaces.  The inverse is the negative-time restriction; no extra
recurrence or minimality assumption is used. -/
def SymbolicLatentModularFlow.orbitClosureFlowHomeomorph
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ) :
    SymbolicLatentModularOrbitClosure Φ x ≃ₜ
      SymbolicLatentModularOrbitClosure Φ (Φ.act t x) where
  toFun := fun y =>
    ⟨Φ.act t y.1, by
      rw [← Φ.actHomeomorph_image_orbitClosure t x]
      exact ⟨y.1, y.2, rfl⟩⟩
  invFun := fun y =>
    ⟨Φ.act (-t) y.1, by
      have hy :
          Φ.act (-t) y.1 ∈
            Φ.orbitClosure (Φ.act (-t) (Φ.act t x)) := by
        rw [← Φ.actHomeomorph_image_orbitClosure (-t) (Φ.act t x)]
        exact ⟨y.1, y.2, rfl⟩
      have hzero : Φ.act (-t) (Φ.act t x) = x := by
        calc
          Φ.act (-t) (Φ.act t x) = Φ.act (-t + t) x :=
            (Φ.add_apply (-t) t x).symm
          _ = x := by rw [neg_add_cancel, Φ.zero_apply]
      rwa [hzero] at hy⟩
  left_inv := by
    intro y
    apply Subtype.ext
    dsimp
    calc
      Φ.act (-t) (Φ.act t y.1) = Φ.act (-t + t) y.1 :=
        (Φ.add_apply (-t) t y.1).symm
      _ = y.1 := by rw [neg_add_cancel, Φ.zero_apply]
  right_inv := by
    intro y
    apply Subtype.ext
    dsimp
    calc
      Φ.act t (Φ.act (-t) y.1) = Φ.act (t + -t) y.1 :=
        (Φ.add_apply t (-t) y.1).symm
      _ = y.1 := by rw [add_neg_cancel, Φ.zero_apply]
  continuous_toFun :=
    ((Φ.actHomeomorph t).continuous_toFun.comp continuous_subtype_val).subtype_mk
      (fun y => by
        rw [← Φ.actHomeomorph_image_orbitClosure t x]
        exact ⟨y.1, y.2, rfl⟩)
  continuous_invFun :=
    ((Φ.actHomeomorph (-t)).continuous_toFun.comp continuous_subtype_val).subtype_mk
      (fun y => by
        have hy :
            Φ.act (-t) y.1 ∈
              Φ.orbitClosure (Φ.act (-t) (Φ.act t x)) := by
          rw [← Φ.actHomeomorph_image_orbitClosure (-t) (Φ.act t x)]
          exact ⟨y.1, y.2, rfl⟩
        have hzero : Φ.act (-t) (Φ.act t x) = x := by
          calc
            Φ.act (-t) (Φ.act t x) = Φ.act (-t + t) x :=
              (Φ.add_apply (-t) t x).symm
            _ = x := by rw [neg_add_cancel, Φ.zero_apply]
        rwa [hzero] at hy)

omit [CompactSpace X] in
@[simp] theorem SymbolicLatentModularFlow.orbitClosureFlowHomeomorph_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ)
    (y : SymbolicLatentModularOrbitClosure Φ x) :
    Φ.orbitClosureFlowHomeomorph x t y =
      ⟨Φ.act t y.1, by
        rw [← Φ.actHomeomorph_image_orbitClosure t x]
        exact ⟨y.1, y.2, rfl⟩⟩ :=
  rfl

omit [CompactSpace X] in
@[simp] theorem SymbolicLatentModularFlow.orbitClosureFlowHomeomorph_symm_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ)
    (y : SymbolicLatentModularOrbitClosure Φ (Φ.act t x)) :
    (Φ.orbitClosureFlowHomeomorph x t).symm y =
      ⟨Φ.act (-t) y.1, by
        have hy :
            Φ.act (-t) y.1 ∈
              Φ.orbitClosure (Φ.act (-t) (Φ.act t x)) := by
          rw [← Φ.actHomeomorph_image_orbitClosure (-t) (Φ.act t x)]
          exact ⟨y.1, y.2, rfl⟩
        have hzero : Φ.act (-t) (Φ.act t x) = x := by
          calc
            Φ.act (-t) (Φ.act t x) = Φ.act (-t + t) x :=
              (Φ.add_apply (-t) t x).symm
            _ = x := by rw [neg_add_cancel, Φ.zero_apply]
        rwa [hzero] at hy⟩ := by
  rfl

omit [CompactSpace X] in
theorem SymbolicLatentModularFlow.orbitClosureFlowHomeomorph_comp_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) (s t : ℝ) :
    ∀ y : SymbolicLatentModularOrbitClosure Φ x,
      ((Φ.orbitClosureFlowHomeomorph x s).trans
        (Φ.orbitClosureFlowHomeomorph (Φ.act s x) t) y).1 =
      Φ.act (t + s) y.1 := by
  intro y
  change Φ.act t (Φ.act s y.1) = Φ.act (t + s) y.1
  simpa using (Φ.add_apply t s y.1).symm

omit [CompactSpace X] in
theorem SymbolicLatentModularFlow.orbitClosureFlowHomeomorph_trans_val_eq
    (Φ : SymbolicLatentModularFlow X) (x : X) (s t : ℝ)
    (y : SymbolicLatentModularOrbitClosure Φ x) :
    ((Φ.orbitClosureFlowHomeomorph x s).trans
        (Φ.orbitClosureFlowHomeomorph (Φ.act s x) t) y).1 =
      (Φ.orbitClosureFlowHomeomorph x (t + s) y).1 := by
  simpa [SymbolicLatentModularFlow.orbitClosureFlowHomeomorph_apply] using
    (Φ.orbitClosureFlowHomeomorph_comp_apply x s t y)

theorem SymbolicLatentModularFlow.orbitClosureFlowHomeomorph_compHausHom_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ)
    (y : SymbolicLatentModularOrbitClosure Φ x) :
    Φ.orbitClosureFlowCompHausHom x t y =
      Φ.orbitClosureFlowHomeomorph x t y :=
  rfl

/-- A time slice induces an isomorphism of compact Hausdorff orbit closures. -/
noncomputable def SymbolicLatentModularFlow.orbitClosureFlowCompHausIso
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ) :
    symbolicLatentModularOrbitClosureCompHaus Φ x ≅
      symbolicLatentModularOrbitClosureCompHaus Φ (Φ.act t x) :=
by
  letI : CompactSpace (SymbolicLatentModularOrbitClosure Φ x) :=
    isCompact_iff_compactSpace.mp (Φ.isCompact_orbitClosure x)
  letI : CompactSpace (SymbolicLatentModularOrbitClosure Φ (Φ.act t x)) :=
    isCompact_iff_compactSpace.mp (Φ.isCompact_orbitClosure (Φ.act t x))
  dsimp [symbolicLatentModularOrbitClosureCompHaus]
  change CompHaus.of (SymbolicLatentModularOrbitClosure Φ x) ≅
    CompHaus.of (SymbolicLatentModularOrbitClosure Φ (Φ.act t x))
  let e := Φ.orbitClosureFlowHomeomorph x t
  exact
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

@[simp] theorem SymbolicLatentModularFlow.orbitClosureFlowCompHausIso_hom_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ)
    (y : symbolicLatentModularOrbitClosureCompHaus Φ x) :
    (Φ.orbitClosureFlowCompHausIso x t).hom y =
      ⟨Φ.act t y.1, by
        rw [← Φ.actHomeomorph_image_orbitClosure t x]
        exact ⟨y.1, y.2, rfl⟩⟩ :=
  rfl

@[simp] theorem SymbolicLatentModularFlow.orbitClosureFlowCompHausIso_inv_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ)
    (y : symbolicLatentModularOrbitClosureCompHaus Φ (Φ.act t x)) :
    (Φ.orbitClosureFlowCompHausIso x t).inv y =
      ⟨Φ.act (-t) y.1, by
        have hy :
            Φ.act (-t) y.1 ∈ Φ.orbitClosure (Φ.act (-t) (Φ.act t x)) := by
          rw [← Φ.actHomeomorph_image_orbitClosure (-t) (Φ.act t x)]
          exact ⟨y.1, y.2, rfl⟩
        have hzero : Φ.act (-t) (Φ.act t x) = x := by
          calc
            Φ.act (-t) (Φ.act t x) = Φ.act (-t + t) x :=
              (Φ.add_apply (-t) t x).symm
            _ = x := by rw [neg_add_cancel, Φ.zero_apply]
        rwa [hzero] at hy⟩ :=
  rfl

theorem SymbolicLatentModularFlow.orbitClosureFlowCompHausIso_hom_inv_id
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ) :
    (Φ.orbitClosureFlowCompHausIso x t).hom ≫
        (Φ.orbitClosureFlowCompHausIso x t).inv =
      𝟙 (symbolicLatentModularOrbitClosureCompHaus Φ x) := by
  ext y
  simp

@[simp] theorem SymbolicLatentModularFlow.orbitClosureFlowCompHausIso_hom_inv_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ)
    (y : symbolicLatentModularOrbitClosureCompHaus Φ x) :
    (((Φ.orbitClosureFlowCompHausIso x t).hom ≫
        (Φ.orbitClosureFlowCompHausIso x t).inv) y).1 =
      y.1 := by
  exact congrArg Subtype.val <|
    congrArg (fun f => f y)
      (Φ.orbitClosureFlowCompHausIso_hom_inv_id x t)

theorem SymbolicLatentModularFlow.orbitClosureFlowCompHausIso_inv_hom_id
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ) :
    (Φ.orbitClosureFlowCompHausIso x t).inv ≫
        (Φ.orbitClosureFlowCompHausIso x t).hom =
      𝟙 (symbolicLatentModularOrbitClosureCompHaus Φ (Φ.act t x)) := by
  ext y
  simp

@[simp] theorem SymbolicLatentModularFlow.orbitClosureFlowCompHausIso_inv_hom_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) (t : ℝ)
    (y : symbolicLatentModularOrbitClosureCompHaus Φ (Φ.act t x)) :
    (((Φ.orbitClosureFlowCompHausIso x t).inv ≫
        (Φ.orbitClosureFlowCompHausIso x t).hom) y).1 =
      y.1 := by
  exact congrArg Subtype.val <|
    congrArg (fun f => f y)
      (Φ.orbitClosureFlowCompHausIso_inv_hom_id x t)

theorem SymbolicLatentModularFlow.orbitClosureFlowCompHausIso_trans_val_eq
    (Φ : SymbolicLatentModularFlow X) (x : X) (s t : ℝ)
    (y : symbolicLatentModularOrbitClosureCompHaus Φ x) :
    (((Φ.orbitClosureFlowCompHausIso x s).hom ≫
      (Φ.orbitClosureFlowCompHausIso (Φ.act s x) t).hom) y).1 =
    ((Φ.orbitClosureFlowCompHausIso x (t + s)).hom y).1 := by
  change ((Φ.orbitClosureFlowHomeomorph x s).trans
      (Φ.orbitClosureFlowHomeomorph (Φ.act s x) t) y).1 =
    (Φ.orbitClosureFlowHomeomorph x (t + s) y).1
  simpa using (Φ.orbitClosureFlowHomeomorph_trans_val_eq x s t y)

theorem SymbolicLatentModularFlow.orbitClosureFlowCompHausIso_comp_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) (s t : ℝ)
    (y : symbolicLatentModularOrbitClosureCompHaus Φ x) :
    (((Φ.orbitClosureFlowCompHausIso x s).hom ≫
        (Φ.orbitClosureFlowCompHausIso (Φ.act s x) t).hom) y).1 =
      ((Φ.orbitClosureFlowCompHausIso x (t + s)).hom y).1 := by
  simpa using Φ.orbitClosureFlowCompHausIso_trans_val_eq x s t y

@[simp] theorem SymbolicLatentModularFlow.orbitClosureFlowCompHausHom_zero_apply
    (Φ : SymbolicLatentModularFlow X) (x : X) :
    ∀ y : symbolicLatentModularOrbitClosureCompHaus Φ x,
      (Φ.orbitClosureFlowCompHausHom x 0 y).1 = y.1 := by
  intro y
  change Φ.act 0 y.1 = y.1
  simpa using Φ.zero_apply y.1

end InfoGeometry.Topology

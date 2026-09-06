import InfoGeometry.Topology.SymbolicLatentObservationRangeCompHaus
import InfoGeometry.Topology.SymbolicLatentObservationQuotientFlowTopCat
import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Compact-Hausdorff flow on the observational range

The quotient-flow owner already provides a continuous time slice on the
observational quotient.  For compact symbolic-latent systems, this file
transports that flow through the canonical quotient-range homeomorphism and
packages the result as a genuine `CompHaus` endomorphism of the observation
range.  No extra dynamical property is added.
-/

noncomputable section

namespace InfoGeometry.Topology

open CategoryTheory

variable {X : Type} [TopologicalSpace X] [CompactSpace X]
variable {ι : Type} [Fintype ι]

noncomputable def SymbolicLatentObservableModularFlow.observationQuotientRangeFlowHomeomorph
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
  (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    Set.range (symbolicObservationQuotientMap S) ≃ₜ
      Set.range (symbolicObservationQuotientMap S) := by
  let e := symbolicObservationQuotientRangeCompactHomeomorph (X := X) (ι := ι) S
  exact (e.symm.trans (Φ.observationQuotientFlowHomeomorph h_cont t)).trans e

noncomputable def SymbolicLatentObservableModularFlow.observationQuotientRangeFlowTopCatHom
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    TopCat.of (Set.range (symbolicObservationQuotientMap S)) ⟶
      TopCat.of (Set.range (symbolicObservationQuotientMap S)) :=
  TopCat.ofHom
    { toFun := Φ.observationQuotientRangeFlowHomeomorph S h_cont t
      continuous_toFun :=
        (Φ.observationQuotientRangeFlowHomeomorph S h_cont t).continuous }

theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowTopCatHom_apply
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ)
    (q : Set.range (symbolicObservationQuotientMap S)) :
    Φ.observationQuotientRangeFlowTopCatHom S h_cont t q =
      Φ.observationQuotientRangeFlowHomeomorph S h_cont t q :=
  rfl

noncomputable def SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausIso
    (S : FiniteSymbolicLatentSystem X ι)
  (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    symbolicObservationRangeCompHaus S ≅
      symbolicObservationRangeCompHaus S := by
  let e := Φ.observationQuotientRangeFlowHomeomorph S h_cont t
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
        intro q
        change e (e.symm q) = q
        exact e.apply_symm_apply q }

noncomputable def SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausHom
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    symbolicObservationRangeCompHaus S ⟶
      symbolicObservationRangeCompHaus S :=
  ⟨Φ.observationQuotientRangeFlowTopCatHom S h_cont t⟩

theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausHom_forget
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    compHausToTop.map (Φ.observationQuotientRangeFlowCompHausHom S h_cont t) =
      Φ.observationQuotientRangeFlowTopCatHom S h_cont t := by
  rfl

theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausHom_isIso
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
    IsIso (Φ.observationQuotientRangeFlowCompHausHom S h_cont t) := by
  have hTopIso : IsIso (Φ.observationQuotientRangeFlowTopCatHom S h_cont t) := by
    simpa [SymbolicLatentObservableModularFlow.observationQuotientRangeFlowTopCatHom]
      using (TopCat.isoOfHomeo
        (X := TopCat.of (Set.range (symbolicObservationQuotientMap S)))
        (Y := TopCat.of (Set.range (symbolicObservationQuotientMap S)))
        (Φ.observationQuotientRangeFlowHomeomorph S h_cont t)).isIso_hom
  haveI : IsIso (compHausToTop.map (Φ.observationQuotientRangeFlowCompHausHom S h_cont t)) := by
    simpa [SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausHom_forget]
      using hTopIso
  have hFF : (compHausToTop).FullyFaithful := by
    simpa using (CompHausLike.fullyFaithfulCompHausLikeToTop (fun _ => True))
  exact hFF.isIso_of_isIso_map (Φ.observationQuotientRangeFlowCompHausHom S h_cont t)

theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowHomeomorph_comp
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
  (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (s t : ℝ) :
    ∀ q : symbolicObservationRangeCompHaus S, ∀ x : ι,
      (((Φ.observationQuotientRangeFlowHomeomorph S h_cont s).trans
        (Φ.observationQuotientRangeFlowHomeomorph S h_cont t) q).1 x) =
      ((Φ.observationQuotientRangeFlowHomeomorph S h_cont (t + s) q).1 x) := by
  intro q x
  change
    ((symbolicObservationQuotientRangeCompactHomeomorph (X := X) (ι := ι) S)
        ((symbolicLatentObservationQuotientFlow Φ h_cont).actHomeomorph t
          ((symbolicObservationQuotientRangeCompactHomeomorph (X := X) (ι := ι) S).symm
            ((symbolicObservationQuotientRangeCompactHomeomorph (X := X) (ι := ι) S)
              ((symbolicLatentObservationQuotientFlow Φ h_cont).actHomeomorph s
                ((symbolicObservationQuotientRangeCompactHomeomorph (X := X) (ι := ι) S).symm q)))))).1 x =
    ((symbolicObservationQuotientRangeCompactHomeomorph (X := X) (ι := ι) S)
        ((symbolicLatentObservationQuotientFlow Φ h_cont).actHomeomorph (t + s)
          ((symbolicObservationQuotientRangeCompactHomeomorph (X := X) (ι := ι) S).symm q))).1 x
  simpa [SymbolicLatentObservableModularFlow.observationQuotientFlowHomeomorph,
    SymbolicLatentObservableModularFlow.observationQuotientFlowHomeomorph_apply,
    SymbolicLatentFlowQuotient.actHomeomorph_apply,
    Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply] using
    congrArg (fun r =>
      (symbolicObservationQuotientRangeCompactHomeomorph (X := X) (ι := ι) S r).1 x)
      ((symbolicLatentObservationQuotientFlow Φ h_cont).actHomeomorph_add_apply t s
        ((symbolicObservationQuotientRangeCompactHomeomorph (X := X) (ι := ι) S).symm q)).symm

@[simp] theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowHomeomorph_comp_apply
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (s t : ℝ) (q : symbolicObservationRangeCompHaus S) :
    (Φ.observationQuotientRangeFlowHomeomorph S h_cont s).trans
        (Φ.observationQuotientRangeFlowHomeomorph S h_cont t) q =
      Φ.observationQuotientRangeFlowHomeomorph S h_cont (t + s) q := by
  ext x
  exact SymbolicLatentObservableModularFlow.observationQuotientRangeFlowHomeomorph_comp
    S Φ h_cont s t q x

@[simp] theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausIso_hom_apply
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ)
    (q : symbolicObservationRangeCompHaus S) :
    (Φ.observationQuotientRangeFlowCompHausIso S h_cont t).hom q =
      Φ.observationQuotientRangeFlowCompHausHom S h_cont t q := by
  rfl

@[simp] theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausIso_inv_apply
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ)
    (q : symbolicObservationRangeCompHaus S) :
    (Φ.observationQuotientRangeFlowCompHausIso S h_cont t).inv q =
    (Φ.observationQuotientRangeFlowCompHausIso S h_cont (-t)).hom q := by
  rfl

theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausIso_hom_inv_id
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
  (Φ.observationQuotientRangeFlowCompHausIso S h_cont t).hom ≫
        (Φ.observationQuotientRangeFlowCompHausIso S h_cont t).inv =
      𝟙 _ := by
  exact (Φ.observationQuotientRangeFlowCompHausIso S h_cont t).hom_inv_id

@[simp] theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausIso_hom_inv_apply
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ)
    (q : symbolicObservationRangeCompHaus S) :
    (((Φ.observationQuotientRangeFlowCompHausIso S h_cont t).hom ≫
        (Φ.observationQuotientRangeFlowCompHausIso S h_cont t).inv) q).1 =
      q.1 := by
  exact congrArg Subtype.val <|
    congrArg (fun f => f q)
      ((Φ.observationQuotientRangeFlowCompHausIso S h_cont t).hom_inv_id)

theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausIso_inv_hom_id
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ) :
  (Φ.observationQuotientRangeFlowCompHausIso S h_cont t).inv ≫
        (Φ.observationQuotientRangeFlowCompHausIso S h_cont t).hom =
      𝟙 _ := by
  exact (Φ.observationQuotientRangeFlowCompHausIso S h_cont t).inv_hom_id

@[simp] theorem SymbolicLatentObservableModularFlow.observationQuotientRangeFlowCompHausIso_inv_hom_apply
    (S : FiniteSymbolicLatentSystem X ι)
    (Φ : SymbolicLatentObservableModularFlow S)
    (h_cont : Continuous (fun p : ℝ × SymbolicLatentObservationQuotient S =>
      descendedSymbolicLatentObservationFlow Φ p.1 p.2))
    (t : ℝ)
    (q : symbolicObservationRangeCompHaus S) :
    (((Φ.observationQuotientRangeFlowCompHausIso S h_cont t).inv ≫
        (Φ.observationQuotientRangeFlowCompHausIso S h_cont t).hom) q).1 =
      q.1 := by
  exact congrArg Subtype.val <|
    congrArg (fun f => f q)
      ((Φ.observationQuotientRangeFlowCompHausIso S h_cont t).inv_hom_id)

end InfoGeometry.Topology

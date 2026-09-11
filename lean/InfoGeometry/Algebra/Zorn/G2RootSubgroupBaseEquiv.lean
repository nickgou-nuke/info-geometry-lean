import InfoGeometry.Algebra.Zorn.G2RootSubgroup
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoOuterGenerators
import InfoGeometry.Algebra.Zorn.G2TwoExplicitGenerators
import InfoGeometry.Algebra.Zorn.G2RootAutShortOneMatrix

namespace InfoGeometry.Algebra.Zorn.G2RootSubgroupBaseEquiv

open InfoGeometry.Algebra.Zorn.G2RootSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2TwoOuterGenerators
open InfoGeometry.Algebra.Zorn.G2Unipotent
open InfoGeometry.Algebra.Zorn.G2RootAutShortOneMatrix
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def baseLongRoot : G2Root := (RootLength.Long, 0)

theorem rootSubgroup_eq_rec_val {α β : G2Root} (h : α = β)
    (x : rootSubgroup α) :
    ((Eq.rec x (congrArg rootSubgroup h) : rootSubgroup β).val) = x.val := by
  cases h
  rfl

theorem rootSubgroupEquiv_cast_apply_val {α β : G2Root} (h : α = β)
    (e : Bool ≃ rootSubgroup α) (t : Bool) :
    ((cast (congrArg (fun r : G2Root => Bool ≃ rootSubgroup r) h) e) t :
      SplitOctF2Aut) = (e t : SplitOctF2Aut) := by
  cases h
  rfl

theorem baseLongRoot_rootAut : rootAut baseLongRoot = g4Aut := by
  rfl

noncomputable def baseLongRootSubgroupMap : Bool → rootSubgroup baseLongRoot :=
  fun t => ⟨xRoot baseLongRoot t, by
    cases t
    · exact Or.inl rfl
    · exact Or.inr (by rw [xRoot_true, baseLongRoot_rootAut])⟩

theorem baseLongRootSubgroupMap_injective :
    Function.Injective baseLongRootSubgroupMap := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exfalso
    have hval : xRoot baseLongRoot false = xRoot baseLongRoot true := by
      exact congrArg Subtype.val h
    rw [xRoot_false, xRoot_true, baseLongRoot_rootAut] at hval
    exact g4Aut_ne_one hval.symm
  · exfalso
    have hval : xRoot baseLongRoot true = xRoot baseLongRoot false := by
      exact congrArg Subtype.val h
    rw [xRoot_true, xRoot_false, baseLongRoot_rootAut] at hval
    exact g4Aut_ne_one hval
  · rfl

theorem baseLongRootSubgroupMap_surjective :
    Function.Surjective baseLongRootSubgroupMap := by
  intro x
  rcases x.property with h | h
  · exact ⟨false, by apply Subtype.ext; simpa [baseLongRootSubgroupMap, xRoot_false] using h.symm⟩
  · exact ⟨true, by apply Subtype.ext; simpa [baseLongRootSubgroupMap, xRoot_true,
      baseLongRoot_rootAut] using h.symm⟩

noncomputable def baseLongRootSubgroupEquiv :
    Bool ≃ rootSubgroup baseLongRoot :=
  Equiv.ofBijective baseLongRootSubgroupMap
    ⟨baseLongRootSubgroupMap_injective, baseLongRootSubgroupMap_surjective⟩

theorem baseLongRootSubgroup_card :
    Nat.card (rootSubgroup baseLongRoot) = 2 := by
  simpa using (Nat.card_congr baseLongRootSubgroupEquiv).symm

theorem rootSubgroup_c_card (α : G2Root) :
    Nat.card (rootSubgroup (cAction α)) = Nat.card (rootSubgroup α) := by
  simpa using (Nat.card_congr (rootSubgroupEquiv_c α).toEquiv).symm

noncomputable def baseLongRoot_c_subgroupEquiv :
    Bool ≃ rootSubgroup (cAction baseLongRoot) :=
  baseLongRootSubgroupEquiv.trans (rootSubgroupEquiv_c baseLongRoot).toEquiv

theorem baseLongRoot_c_card :
    Nat.card (rootSubgroup (cAction baseLongRoot)) = 2 := by
  simpa using (Nat.card_congr baseLongRoot_c_subgroupEquiv).symm

noncomputable def rootSubgroupEquiv_s (α : G2Root) :
    rootSubgroup α ≃* rootSubgroup (sAction α) :=
  rootSubgroupConjEquiv_of_aut
    InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2.s α (sAction α) (s_rootAut_s α)

theorem rootSubgroup_s_card (α : G2Root) :
    Nat.card (rootSubgroup (sAction α)) = Nat.card (rootSubgroup α) := by
  simpa using (Nat.card_congr (rootSubgroupEquiv_s α).toEquiv).symm

noncomputable def baseLongRoot_s_subgroupEquiv :
    Bool ≃ rootSubgroup (sAction baseLongRoot) :=
  baseLongRootSubgroupEquiv.trans
    (rootSubgroupEquiv_s baseLongRoot).toEquiv

theorem baseLongRoot_s_card :
    Nat.card (rootSubgroup (sAction baseLongRoot)) = 2 := by
  simpa using (Nat.card_congr baseLongRoot_s_subgroupEquiv).symm

def cIterRoot : Nat → G2Root
  | 0 => baseLongRoot
  | n + 1 => cAction (cIterRoot n)

theorem cIterRoot_six_eq_baseLongRoot :
    cIterRoot 6 = baseLongRoot := by
  decide

theorem cIterRoot_fin_eq_longRoot (i : Fin 6) :
    cIterRoot i.val = (RootLength.Long, (i : ZMod 6)) := by
  fin_cases i <;> decide

noncomputable def cIterRootSubgroupEquiv :
    (n : Nat) → Bool ≃ rootSubgroup (cIterRoot n)
  | 0 => baseLongRootSubgroupEquiv
  | n + 1 =>
      (cIterRootSubgroupEquiv n).trans
        (rootSubgroupEquiv_c (cIterRoot n)).toEquiv

theorem cIterRootSubgroup_card (n : Nat) :
    Nat.card (rootSubgroup (cIterRoot n)) = 2 := by
  simpa using (Nat.card_congr (cIterRootSubgroupEquiv n)).symm

noncomputable def longRootSubgroupEquiv (i : Fin 6) :
    Bool ≃ rootSubgroup (RootLength.Long, (i : ZMod 6)) := by
  rw [← cIterRoot_fin_eq_longRoot i]
  exact cIterRootSubgroupEquiv i.val

theorem longRootSubgroup_card (i : Fin 6) :
    Nat.card (rootSubgroup (RootLength.Long, (i : ZMod 6))) = 2 := by
  simpa using (Nat.card_congr (longRootSubgroupEquiv i)).symm

theorem cIterRoot_three_eq_neg_baseLongRoot :
    cIterRoot 3 = negAction baseLongRoot := by
  decide

noncomputable def negBaseLongRootSubgroupEquiv :
    Bool ≃ rootSubgroup (negAction baseLongRoot) := by
  rw [← cIterRoot_three_eq_neg_baseLongRoot]
  exact cIterRootSubgroupEquiv 3

theorem negBaseLongRootSubgroup_card :
    Nat.card (rootSubgroup (negAction baseLongRoot)) = 2 := by
  simpa using (Nat.card_congr negBaseLongRootSubgroupEquiv).symm

def baseShortRoot : G2Root := (RootLength.Short, 0)

theorem rootAut_ne_one (α : G2Root) : rootAut α ≠ (1 : SplitOctF2Aut) := by
  rcases α with ⟨length, k⟩
  cases length
  · simpa [rootAut, S0, conjugateAut] using
      conjugateAut_ne_one (c ^ k.val) (unipotentShortAut true)
        unipotentShortAut_true_ne_one
  · simpa [rootAut, L0, conjugateAut] using
      conjugateAut_ne_one (c ^ k.val) (g4Aut) g4Aut_ne_one

noncomputable def rootSubgroupMap (α : G2Root) :
    Bool → rootSubgroup α :=
  fun t => ⟨xRoot α t, by
    cases t
    · exact Or.inl rfl
    · exact Or.inr (xRoot_true α)⟩

theorem rootSubgroupMap_injective (α : G2Root) :
    Function.Injective (rootSubgroupMap α) := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exfalso
    have hval : xRoot α false = xRoot α true := congrArg Subtype.val h
    rw [xRoot_false, xRoot_true] at hval
    exact rootAut_ne_one α hval.symm
  · exfalso
    have hval : xRoot α true = xRoot α false := congrArg Subtype.val h
    rw [xRoot_true, xRoot_false] at hval
    exact rootAut_ne_one α hval
  · rfl

theorem rootSubgroupMap_surjective (α : G2Root) :
    Function.Surjective (rootSubgroupMap α) := by
  intro x
  rcases x.property with h | h
  · exact ⟨false, by apply Subtype.ext; simpa [rootSubgroupMap,
      xRoot_false] using h.symm⟩
  · exact ⟨true, by apply Subtype.ext; simpa [rootSubgroupMap,
      xRoot_true] using h.symm⟩

noncomputable def rootSubgroupEquivBool (α : G2Root) :
    Bool ≃ rootSubgroup α :=
  Equiv.ofBijective (rootSubgroupMap α)
    ⟨rootSubgroupMap_injective α, rootSubgroupMap_surjective α⟩

theorem rootSubgroupEquivBool_apply (α : G2Root) (t : Bool) :
    (rootSubgroupEquivBool α t).val = xRoot α t := by
  rfl

noncomputable def longRootSubgroupEquivNative (i : Fin 6) :
    Bool ≃ rootSubgroup (RootLength.Long, (i : ZMod 6)) :=
  rootSubgroupEquivBool (RootLength.Long, (i : ZMod 6))

theorem longRootSubgroupEquivNative_apply (i : Fin 6) (t : Bool) :
    (longRootSubgroupEquivNative i t).val =
      xRoot (RootLength.Long, (i : ZMod 6)) t := by
  exact rootSubgroupEquivBool_apply (RootLength.Long, (i : ZMod 6)) t

theorem longRootSubgroupEquivNative_card (i : Fin 6) :
    Nat.card (rootSubgroup (RootLength.Long, (i : ZMod 6))) = 2 := by
  simpa using (Nat.card_congr (longRootSubgroupEquivNative i)).symm

theorem rootSubgroupEquiv_c_apply (α : G2Root) (t : Bool) :
    (rootSubgroupEquiv_c α).toEquiv (rootSubgroupEquivBool α t) =
      rootSubgroupEquivBool (cAction α) t := by
  apply Subtype.ext
  change c * xRoot α t * c⁻¹ = xRoot (cAction α) t
  exact c_xRoot_c α t

theorem cIterRootSubgroupEquiv_coe_eq_xRoot (n : Nat) (t : Bool) :
    (cIterRootSubgroupEquiv n t : SplitOctF2Aut) = xRoot (cIterRoot n) t := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [cIterRootSubgroupEquiv, Equiv.trans_apply, cIterRoot]
      have hsub : cIterRootSubgroupEquiv n t =
          rootSubgroupEquivBool (cIterRoot n) t := by
        apply Subtype.ext
        exact ih
      rw [hsub]
      have h := congrArg (fun z : rootSubgroup (cAction (cIterRoot n)) =>
          (z : SplitOctF2Aut)) (rootSubgroupEquiv_c_apply (cIterRoot n) t)
      simpa only [rootSubgroupEquivBool_apply] using h

theorem rootSubgroupEquiv_s_apply (α : G2Root) (t : Bool) :
    (rootSubgroupEquiv_s α).toEquiv (rootSubgroupEquivBool α t) =
      rootSubgroupEquivBool (sAction α) t := by
  apply Subtype.ext
  change s * xRoot α t * s⁻¹ = xRoot (sAction α) t
  have hs : s⁻¹ = s := by
    apply mul_left_cancel (a := s)
    simp [s_sq]
  rw [hs]
  exact s_xRoot_s α t

theorem rootAut_short_one_corrected_pc_alignment :
    rootAut (RootLength.Short, (1 : ZMod 6)) =
      G2TwoSylowSubgroup.pcWord shortOneCorrectedPCExp := by
  exact rootAut_short_one_eq_correctedPCWord

theorem rootAut_short_two_corrected_pc_alignment :
    rootAut (RootLength.Short, (2 : ZMod 6)) =
      G2TwoSylowSubgroup.pcWord shortTwoCorrectedPCExp := by
  exact rootAut_short_two_eq_correctedPCWord

theorem rootAut_short_three_pc_alignment :
    rootAut (RootLength.Short, (3 : ZMod 6)) =
      G2TwoSylowPCAutomorphisms.pc2Aut *
        G2TwoSylowPCAutomorphisms.pc5Aut *
        G2TwoSylowPCAutomorphisms.pc6Aut := by
  exact rootAut_short_three_eq_pcWord

theorem rootSubgroup_card (α : G2Root) :
    Nat.card (rootSubgroup α) = 2 := by
  simpa using (Nat.card_congr (rootSubgroupEquivBool α)).symm

theorem baseShortRoot_rootAut : rootAut baseShortRoot = unipotentShortAut true := by
  rfl

noncomputable def baseShortRootSubgroupMap : Bool → rootSubgroup baseShortRoot :=
  fun t => ⟨xRoot baseShortRoot t, by
    cases t
    · exact Or.inl rfl
    · exact Or.inr (by rw [xRoot_true, baseShortRoot_rootAut])⟩

theorem baseShortRootSubgroupMap_injective :
    Function.Injective baseShortRootSubgroupMap := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exfalso
    have hval : xRoot baseShortRoot false = xRoot baseShortRoot true :=
      congrArg Subtype.val h
    rw [xRoot_false, xRoot_true, baseShortRoot_rootAut] at hval
    exact unipotentShortAut_true_ne_one hval.symm
  · exfalso
    have hval : xRoot baseShortRoot true = xRoot baseShortRoot false :=
      congrArg Subtype.val h
    rw [xRoot_true, xRoot_false, baseShortRoot_rootAut] at hval
    exact unipotentShortAut_true_ne_one hval
  · rfl

theorem baseShortRootSubgroupMap_surjective :
    Function.Surjective baseShortRootSubgroupMap := by
  intro x
  rcases x.property with h | h
  · exact ⟨false, by apply Subtype.ext; simpa [baseShortRootSubgroupMap,
      xRoot_false] using h.symm⟩
  · exact ⟨true, by apply Subtype.ext; simpa [baseShortRootSubgroupMap,
      xRoot_true, baseShortRoot_rootAut] using h.symm⟩

noncomputable def baseShortRootSubgroupEquiv :
    Bool ≃ rootSubgroup baseShortRoot :=
  Equiv.ofBijective baseShortRootSubgroupMap
    ⟨baseShortRootSubgroupMap_injective, baseShortRootSubgroupMap_surjective⟩

theorem baseShortRootSubgroup_card :
    Nat.card (rootSubgroup baseShortRoot) = 2 := by
  simpa using (Nat.card_congr baseShortRootSubgroupEquiv).symm

def cIterShortRoot : Nat → G2Root
  | 0 => baseShortRoot
  | n + 1 => cAction (cIterShortRoot n)

theorem cIterShortRoot_six_eq_baseShortRoot :
    cIterShortRoot 6 = baseShortRoot := by
  decide

theorem cIterShortRoot_fin_eq_shortRoot (i : Fin 6) :
    cIterShortRoot i.val = (RootLength.Short, (i : ZMod 6)) := by
  fin_cases i <;> decide

noncomputable def cIterShortRootSubgroupEquiv :
    (n : Nat) → Bool ≃ rootSubgroup (cIterShortRoot n)
  | 0 => baseShortRootSubgroupEquiv
  | n + 1 =>
      (cIterShortRootSubgroupEquiv n).trans
        (rootSubgroupEquiv_c (cIterShortRoot n)).toEquiv

theorem cIterShortRootSubgroup_card (n : Nat) :
    Nat.card (rootSubgroup (cIterShortRoot n)) = 2 := by
  simpa using (Nat.card_congr (cIterShortRootSubgroupEquiv n)).symm

noncomputable def shortRootSubgroupEquiv (i : Fin 6) :
    Bool ≃ rootSubgroup (RootLength.Short, (i : ZMod 6)) := by
  rw [← cIterShortRoot_fin_eq_shortRoot i]
  exact cIterShortRootSubgroupEquiv i.val

theorem shortRootSubgroup_card (i : Fin 6) :
    Nat.card (rootSubgroup (RootLength.Short, (i : ZMod 6))) = 2 := by
  simpa using (Nat.card_congr (shortRootSubgroupEquiv i)).symm

end InfoGeometry.Algebra.Zorn.G2RootSubgroupBaseEquiv

import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylGroup
import InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
import InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2IndexTwoRankOneBN2

namespace InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector

noncomputable def correctedT : SplitOctF2Aut := concreteWeylElement 11

private theorem correctedT_eq_word :
    correctedT = swapCartanAut * (swap01Aut * (cycle012Aut * cycle012Aut)) := by
  rfl

private theorem correctedT_inv : correctedT⁻¹ = correctedT := by
  rw [correctedT_eq_word]
  apply inv_eq_iff_mul_eq_one.mpr
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> rfl

theorem correctedT_conj_pc1 :
    correctedT⁻¹ * pcGenerator 1 * correctedT =
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => false | 1 => true | 2 => true
        | 3 => true | 4 => false | 5 => false) := by
  rw [correctedT_inv]
  apply automorphism_ext_of_basis
  intro i
  rw [G2TwoSylowSubgroup.pcWord_apply]
  fin_cases i <;>
    simp [correctedT_eq_word, pcWordFun, pcTermFun, pcGenerator,
      swap01Aut_apply, swap01Fun, swapCartanAut, swapCartanEquiv,
      swapCartanFun, cycle012Aut_apply, cycle012Fun,
      G2TwoSylowPCAutomorphisms.pc2Aut,
      G2TwoSylowPCAutomorphisms.pc2Equiv,
      pc2Fun, pc3Fun, pc4Fun, pc6Fun,
      basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

theorem correctedT_conj_pc2 :
    correctedT⁻¹ * pcGenerator 2 * correctedT =
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => false | 1 => true | 2 => true
        | 3 => true | 4 => true | 5 => true) := by
  rw [correctedT_inv]
  apply automorphism_ext_of_basis
  intro i
  rw [G2TwoSylowSubgroup.pcWord_apply]
  fin_cases i <;>
    simp [correctedT_eq_word, pcWordFun, pcTermFun, pcGenerator,
      swap01Aut_apply, swap01Fun, swapCartanAut, swapCartanEquiv,
      swapCartanFun, cycle012Aut_apply, cycle012Fun,
      G2TwoSylowPCAutomorphisms.pc3Aut,
      G2TwoSylowPCAutomorphisms.pc3Equiv,
      pc2Fun, pc3Fun, pc4Fun, pc5Fun, pc6Fun,
      basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

theorem correctedT_conj_pc3 :
    correctedT⁻¹ * pcGenerator 3 * correctedT =
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => false | 1 => true | 2 => false
        | 3 => false | 4 => true | 5 => true) := by
  rw [correctedT_inv]
  apply automorphism_ext_of_basis
  intro i
  rw [G2TwoSylowSubgroup.pcWord_apply]
  fin_cases i <;>
    simp [correctedT_eq_word, pcWordFun, pcTermFun, pcGenerator,
      swap01Aut_apply, swap01Fun, swapCartanAut, swapCartanEquiv,
      swapCartanFun, cycle012Aut_apply, cycle012Fun,
      G2TwoSylowPCAutomorphisms.pc4Aut,
      involutiveEquiv, pc2Fun, pc4Fun, pc5Fun, pc6Fun,
      basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

theorem correctedT_conj_pc4 :
    correctedT⁻¹ * pcGenerator 4 * correctedT =
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => false | 1 => true | 2 => true
        | 3 => false | 4 => false | 5 => false) := by
  rw [correctedT_inv]
  apply automorphism_ext_of_basis
  intro i
  rw [G2TwoSylowSubgroup.pcWord_apply]
  fin_cases i <;>
    simp [correctedT_eq_word, pcWordFun, pcTermFun, pcGenerator,
      swap01Aut_apply, swap01Fun, swapCartanAut, swapCartanEquiv,
      swapCartanFun, cycle012Aut_apply, cycle012Fun,
      G2TwoSylowPCAutomorphisms.pc5Aut,
      involutiveEquiv, pc2Fun, pc3Fun, pc5Fun,
      basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

theorem correctedT_conj_pc5 :
    correctedT⁻¹ * pcGenerator 5 * correctedT =
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => false | 1 => false | 2 => false
        | 3 => false | 4 => false | 5 => true) := by
  rw [correctedT_inv]
  apply automorphism_ext_of_basis
  intro i
  rw [G2TwoSylowSubgroup.pcWord_apply]
  fin_cases i <;>
    simp [correctedT_eq_word, pcWordFun, pcTermFun, pcGenerator,
      swap01Aut_apply, swap01Fun, swapCartanAut, swapCartanEquiv,
      swapCartanFun, cycle012Aut_apply, cycle012Fun,
      G2TwoSylowPCAutomorphisms.pc6Aut,
      involutiveEquiv, pc6Fun,
      basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

def correctedTComplementSubgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure {pcGenerator 1, pcGenerator 2, pcGenerator 3,
    pcGenerator 4, pcGenerator 5}

theorem pcWord_oneAtBit_mem_correctedTComplement (i : Fin 6)
    (hi : i ≠ 0) (b : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit i b) ∈ correctedTComplementSubgroup := by
  rw [pcWord_oneAtBit]
  split
  · fin_cases i
    · exact False.elim (hi rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.one_mem _

theorem pcWord_mem_correctedTComplement (e : PCExponent)
    (he : e 0 = false) :
    G2TwoSylowSubgroup.pcWord e ∈ correctedTComplementSubgroup := by
  rw [pcWord_factorized]
  have h1 := pcWord_oneAtBit_mem_correctedTComplement 1 (by decide) (e 1)
  have h2 := pcWord_oneAtBit_mem_correctedTComplement 2 (by decide) (e 2)
  have h3 := pcWord_oneAtBit_mem_correctedTComplement 3 (by decide) (e 3)
  have h4 := pcWord_oneAtBit_mem_correctedTComplement 4 (by decide) (e 4)
  have h5 := pcWord_oneAtBit_mem_correctedTComplement 5 (by decide) (e 5)
  have h0 : G2TwoSylowSubgroup.pcWord (oneAtBit 0 (e 0)) ∈
      correctedTComplementSubgroup := by
    rw [he]
    change G2TwoSylowSubgroup.pcWord zeroPC ∈ correctedTComplementSubgroup
    rw [pcWord_zeroPC_eq_one]
    exact Subgroup.one_mem _
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ h0 h1) h2) h3) h4) h5

theorem correctedTComplementSubgroup_le_unipotentSubgroup :
    correctedTComplementSubgroup ≤
      InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup := by
  refine (Subgroup.closure_le _).2 ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact G2TwoPCConcreteFacts.pcGenerator_mem_pcWord_range 1
  · exact G2TwoPCConcreteFacts.pcGenerator_mem_pcWord_range 2
  · exact G2TwoPCConcreteFacts.pcGenerator_mem_pcWord_range 3
  · exact G2TwoPCConcreteFacts.pcGenerator_mem_pcWord_range 4
  · exact G2TwoPCConcreteFacts.pcGenerator_mem_pcWord_range 5

theorem correctedT_complement_conj_mem_unipotent
    (h : SplitOctF2Aut) (hh : h ∈ correctedTComplementSubgroup) :
    correctedT⁻¹ * h * correctedT ∈
      InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · rw [correctedT_conj_pc1]
        exact ⟨_, rfl⟩
      · rw [correctedT_conj_pc2]
        exact ⟨_, rfl⟩
      · rw [correctedT_conj_pc3]
        exact ⟨_, rfl⟩
      · rw [correctedT_conj_pc4]
        exact ⟨_, rfl⟩
      · rw [correctedT_conj_pc5]
        exact ⟨_, rfl⟩
  | one =>
      simpa only [_root_.mul_one, _root_.one_mul, inv_mul_cancel] using
        InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup.one_mem
  | mul x y hx hy ihx ihy =>
      have hconj :
          correctedT⁻¹ * (x * y) * correctedT =
            (correctedT⁻¹ * x * correctedT) *
              (correctedT⁻¹ * y * correctedT) := by
        group
      rw [hconj]
      exact InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup.mul_mem ihx ihy
  | inv x hx ihx =>
      have hconj :
          correctedT⁻¹ * x⁻¹ * correctedT =
            (correctedT⁻¹ * x * correctedT)⁻¹ := by
        group
      exact hconj ▸
        InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup.inv_mem ihx

theorem correctedT_rank_one_witness :
    let r : SplitOctF2Aut :=
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => true | 1 => false | 2 => false
        | 3 => true | 4 => false | 5 => false)
    correctedT * r * correctedT = r * correctedT * r := by
  dsimp
  apply automorphism_ext_of_basis
  intro i
  repeat rw [aut_mul_apply]
  repeat rw [pcWord_apply]
  fin_cases i <;>
    simp [correctedT_eq_word, pcWordFun, pcTermFun,
      swap01Aut_apply, swap01Fun, swapCartanAut, swapCartanEquiv,
      swapCartanFun, cycle012Aut_apply, cycle012Fun,
      pc1Fun, pc4Fun,
      basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

def correctedTRankOneExponent : PCExponent := fun i => match i with
  | 0 => true | 1 => false | 2 => false
  | 3 => true | 4 => false | 5 => false

theorem correctedT_borel_split (b : SplitOctF2Aut)
    (hb : b ∈ InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup) :
    b ∈ correctedTComplementSubgroup ∨
      ∃ h ∈ correctedTComplementSubgroup,
        b = G2TwoSylowSubgroup.pcWord correctedTRankOneExponent * h := by
  rcases hb with ⟨e, rfl⟩
  by_cases he : e 0 = false
  · exact Or.inl (pcWord_mem_correctedTComplement e he)
  · have he' : e 0 = true := by
      cases h : e 0 with
      | false => exact False.elim (he h)
      | true => rfl
    let hExp : PCExponent :=
      InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.pcCombine
        (InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.pcInverse correctedTRankOneExponent) e
    have hExp_zero : hExp 0 = false := by
      change (InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.pcCombine
        (InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.pcInverse correctedTRankOneExponent) e) 0 = false
      rw [InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.pcCombine_apply_zero,
        InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.pcInverse_apply_zero, he']
      rfl
    refine Or.inr ⟨G2TwoSylowSubgroup.pcWord hExp,
      pcWord_mem_correctedTComplement hExp hExp_zero, ?_⟩
    symm
    calc
      G2TwoSylowSubgroup.pcWord correctedTRankOneExponent *
          G2TwoSylowSubgroup.pcWord hExp =
          G2TwoSylowSubgroup.pcWord
            (InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.pcCombine
              correctedTRankOneExponent hExp) := by
            rw [_root_.InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector.pcWord_mul_pcWord]
      _ = G2TwoSylowSubgroup.pcWord e := by
        apply congrArg G2TwoSylowSubgroup.pcWord
        dsimp [hExp]
        group

theorem correctedT_sq : correctedT * correctedT = 1 := by
  rw [← correctedT_inv]
  exact inv_mul_cancel _

theorem swap01_correctedT_order_six :
    (swap01Aut * correctedT) ^ 6 = 1 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;>
    rfl

theorem correctedT_concrete_bn2 (b : SplitOctF2Aut)
    (hb : b ∈ InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup) :
    InfoGeometry.Algebra.Zorn.IndexTwoLevi.InBruhatCover
      InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup
      correctedT (correctedT * b * correctedT) := by
  let r : SplitOctF2Aut :=
    G2TwoSylowSubgroup.pcWord correctedTRankOneExponent
  have hr : r ∈ InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup := by
    exact ⟨correctedTRankOneExponent, rfl⟩
  exact InfoGeometry.Algebra.Zorn.IndexTwoLevi.bn2_of_index2_split
    InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup
    correctedTComplementSubgroup correctedT correctedT_sq r hr
    (fun h hh => correctedT_complement_conj_mem_unipotent h hh)
    (by simpa [r] using correctedT_rank_one_witness) b hb
    (correctedT_borel_split b hb)

end InfoGeometry.Algebra.Zorn.G2ConcreteBN2CorrectSecondConjugation

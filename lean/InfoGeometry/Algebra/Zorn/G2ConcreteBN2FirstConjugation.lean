import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylGroup
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2IndexTwoRankOneBN2
import InfoGeometry.Algebra.Zorn.G2IndexTwoRankOneBN2

namespace InfoGeometry.Algebra.Zorn.G2ConcreteBN2FirstConjugation

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector

/- CAS certificate: SymPy and GAP, using the explicit Lean carrier matrices,
   give the word [0,0,1,0,1,1]. -/
theorem swap01_conj_pc0 :
    swap01Aut⁻¹ * pcGenerator 0 * swap01Aut =
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => false | 1 => false | 2 => true
        | 3 => false | 4 => true | 5 => true) := by
  have h_inv : swap01Aut⁻¹ = swap01Aut := by
    rw [inv_eq_iff_mul_eq_one]
    exact swap01Aut_sq
  rw [h_inv]
  apply automorphism_ext_of_basis
  intro i
  rw [aut_mul_apply, pcWord_apply]
  fin_cases i <;>
    simp [pcWordFun, pcTermFun, pcGenerator, swap01Aut_apply, swap01Fun,
      G2TwoSylowPCAutomorphisms.pc1Aut, involutiveEquiv,
      pc1Fun, pc3Fun, pc5Fun, basis8, ePlus, eMinus, up0, up1, up2,
      pc6Fun, down0, down1, down2]

/- CAS certificate: SymPy/GAP word [1,0,0,0,1,1]. -/
theorem swap01_conj_pc2 :
    swap01Aut⁻¹ * pcGenerator 2 * swap01Aut =
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => true | 1 => false | 2 => false
        | 3 => false | 4 => true | 5 => true) := by
  have h_inv : swap01Aut⁻¹ = swap01Aut := by
    rw [inv_eq_iff_mul_eq_one]
    exact swap01Aut_sq
  rw [h_inv]
  apply automorphism_ext_of_basis
  intro i
  rw [pcWord_apply]
  fin_cases i <;>
    simp [pcWordFun, pcTermFun, pcGenerator, swap01Aut_apply, swap01Fun,
      G2TwoSylowPCAutomorphisms.pc3Aut,
      G2TwoSylowPCAutomorphisms.pc3Equiv,
      pc1Fun, pc3Fun, pc5Fun, basis8, ePlus, eMinus, up0, up1, up2,
      pc6Fun, down0, down1, down2]

/- CAS certificate: SymPy/GAP word [0,0,0,0,0,1]. -/
theorem swap01_conj_pc3 :
    swap01Aut⁻¹ * pcGenerator 3 * swap01Aut =
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => false | 1 => false | 2 => false
        | 3 => false | 4 => false | 5 => true) := by
  have h_inv : swap01Aut⁻¹ = swap01Aut := by
    rw [inv_eq_iff_mul_eq_one]
    exact swap01Aut_sq
  rw [h_inv]
  apply automorphism_ext_of_basis
  intro i
  rw [pcWord_apply]
  fin_cases i <;>
    simp [pcWordFun, pcTermFun, pcGenerator, swap01Aut_apply, swap01Fun,
      G2TwoSylowPCAutomorphisms.pc4Aut, involutiveEquiv, pc4Fun, pc6Fun,
      basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

/- CAS certificate: SymPy/GAP word [0,0,0,1,1,1]. -/
theorem swap01_conj_pc4 :
    swap01Aut⁻¹ * pcGenerator 4 * swap01Aut =
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => false | 1 => false | 2 => false
        | 3 => true | 4 => true | 5 => true) := by
  have h_inv : swap01Aut⁻¹ = swap01Aut := by
    rw [inv_eq_iff_mul_eq_one]
    exact swap01Aut_sq
  rw [h_inv]
  apply automorphism_ext_of_basis
  intro i
  rw [pcWord_apply]
  fin_cases i <;>
    simp [pcWordFun, pcTermFun, pcGenerator, swap01Aut_apply, swap01Fun,
      G2TwoSylowPCAutomorphisms.pc5Aut,
      involutiveEquiv, pc4Fun, pc5Fun, pc6Fun,
      basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

/- CAS certificate: SymPy/GAP word [0,0,0,1,0,0]. -/
theorem swap01_conj_pc5 :
    swap01Aut⁻¹ * pcGenerator 5 * swap01Aut =
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => false | 1 => false | 2 => false
        | 3 => true | 4 => false | 5 => false) := by
  have h_inv : swap01Aut⁻¹ = swap01Aut := by
    rw [inv_eq_iff_mul_eq_one]
    exact swap01Aut_sq
  rw [h_inv]
  apply automorphism_ext_of_basis
  intro i
  rw [pcWord_apply]
  fin_cases i <;>
    simp [pcWordFun, pcTermFun, pcGenerator, swap01Aut_apply, swap01Fun,
      G2TwoSylowPCAutomorphisms.pc6Aut,
      involutiveEquiv, pc4Fun, pc6Fun,
      basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

def swap01ComplementSubgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure {pcGenerator 0, pcGenerator 2, pcGenerator 3,
    pcGenerator 4, pcGenerator 5}

theorem pcWord_oneAtBit_mem_swap01ComplementSubgroup (i : Fin 6)
    (hi : i ≠ 1) (b : Bool) :
    G2TwoSylowSubgroup.pcWord (oneAtBit i b) ∈ swap01ComplementSubgroup := by
  rw [pcWord_oneAtBit]
  split
  · fin_cases i
    · exact Subgroup.subset_closure (by simp)
    · exact False.elim (hi rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.one_mem _

theorem pcWord_mem_swap01ComplementSubgroup (e : PCExponent)
    (he : e 1 = false) :
    G2TwoSylowSubgroup.pcWord e ∈ swap01ComplementSubgroup := by
  rw [pcWord_factorized]
  have h0 := pcWord_oneAtBit_mem_swap01ComplementSubgroup 0 (by decide) (e 0)
  have h2 := pcWord_oneAtBit_mem_swap01ComplementSubgroup 2 (by decide) (e 2)
  have h3 := pcWord_oneAtBit_mem_swap01ComplementSubgroup 3 (by decide) (e 3)
  have h4 := pcWord_oneAtBit_mem_swap01ComplementSubgroup 4 (by decide) (e 4)
  have h5 := pcWord_oneAtBit_mem_swap01ComplementSubgroup 5 (by decide) (e 5)
  have h1 : G2TwoSylowSubgroup.pcWord (oneAtBit 1 (e 1)) ∈
      swap01ComplementSubgroup := by
    rw [he]
    change G2TwoSylowSubgroup.pcWord zeroPC ∈ swap01ComplementSubgroup
    rw [pcWord_zeroPC_eq_one]
    exact Subgroup.one_mem _
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ h0 h1) h2) h3) h4) h5

theorem swap01ComplementSubgroup_le_unipotentSubgroup :
    swap01ComplementSubgroup ≤
      InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup := by
  refine (Subgroup.closure_le _).2 ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact G2TwoPCConcreteFacts.pcGenerator_mem_pcWord_range 0
  · exact G2TwoPCConcreteFacts.pcGenerator_mem_pcWord_range 2
  · exact G2TwoPCConcreteFacts.pcGenerator_mem_pcWord_range 3
  · exact G2TwoPCConcreteFacts.pcGenerator_mem_pcWord_range 4
  · exact G2TwoPCConcreteFacts.pcGenerator_mem_pcWord_range 5

theorem swap01ComplementSubgroup_pc_recovery_one_false
    (h : SplitOctF2Aut) (hh : h ∈ swap01ComplementSubgroup)
    (e : PCExponent) (he : G2TwoSylowSubgroup.pcWord e = h) :
    e 1 = false := by
  induction hh using Subgroup.closure_induction generalizing e with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · have heq : e = oneAt 0 := by
          apply G2TwoPCRecoveryTransport.pcWord_injective_concrete
          rw [he, G2TwoPCConcreteFacts.pcWord_oneAt_eq_generator]
        rw [heq]
        rfl
      · have heq : e = oneAt 2 := by
          apply G2TwoPCRecoveryTransport.pcWord_injective_concrete
          rw [he, G2TwoPCConcreteFacts.pcWord_oneAt_eq_generator]
        rw [heq]
        rfl
      · have heq : e = oneAt 3 := by
          apply G2TwoPCRecoveryTransport.pcWord_injective_concrete
          rw [he, G2TwoPCConcreteFacts.pcWord_oneAt_eq_generator]
        rw [heq]
        rfl
      · have heq : e = oneAt 4 := by
          apply G2TwoPCRecoveryTransport.pcWord_injective_concrete
          rw [he, G2TwoPCConcreteFacts.pcWord_oneAt_eq_generator]
        rw [heq]
        rfl
      · have heq : e = oneAt 5 := by
          apply G2TwoPCRecoveryTransport.pcWord_injective_concrete
          rw [he, G2TwoPCConcreteFacts.pcWord_oneAt_eq_generator]
        rw [heq]
        rfl
  | one =>
      have heq : e = zeroPC := by
        apply G2TwoPCRecoveryTransport.pcWord_injective_concrete
        rw [he, G2TwoPCConcreteFacts.pcWord_zeroPC_eq_one]
      rw [heq]
      rfl
  | mul x y hx hy ihx ihy =>
      have hxU := swap01ComplementSubgroup_le_unipotentSubgroup hx
      have hyU := swap01ComplementSubgroup_le_unipotentSubgroup hy
      change x ∈ Set.range G2TwoSylowSubgroup.pcWord at hxU
      change y ∈ Set.range G2TwoSylowSubgroup.pcWord at hyU
      rcases hxU with ⟨ex, hex⟩
      rcases hyU with ⟨ey, hey⟩
      have hex0 : ex 1 = false := ihx ex hex
      have hey0 : ey 1 = false := ihy ey hey
      have hcombine : G2TwoSylowSubgroup.pcWord (pcCombine ex ey) = x * y := by
        rw [← _root_.InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector.pcWord_mul_pcWord,
          hex, hey]
      have heq : e = pcCombine ex ey := by
        apply G2TwoPCRecoveryTransport.pcWord_injective_concrete
        exact he.trans hcombine.symm
      rw [heq, pcCombine_apply_one, hex0, hey0]
      rfl
  | inv x hx ihx =>
      have hxU := swap01ComplementSubgroup_le_unipotentSubgroup hx
      change x ∈ Set.range G2TwoSylowSubgroup.pcWord at hxU
      rcases hxU with ⟨ex, hex⟩
      have hex0 : ex 1 = false := ihx ex hex
      have hinv : G2TwoSylowSubgroup.pcWord (pcInverse ex) = x⁻¹ := by
        rw [← InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.pcWord_inv, hex]
      have heq : e = pcInverse ex := by
        apply G2TwoPCRecoveryTransport.pcWord_injective_concrete
        exact he.trans hinv.symm
      rw [heq, pcInverse_apply_one ex]
      exact hex0

theorem swap01_conj_complement_mem_unipotent
    (h : SplitOctF2Aut) (hh : h ∈ swap01ComplementSubgroup) :
    swap01Aut⁻¹ * h * swap01Aut ∈
      InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · rw [swap01_conj_pc0]
        exact ⟨_, rfl⟩
      · rw [swap01_conj_pc2]
        exact ⟨_, rfl⟩
      · rw [swap01_conj_pc3]
        exact ⟨_, rfl⟩
      · rw [swap01_conj_pc4]
        exact ⟨_, rfl⟩
      · rw [swap01_conj_pc5]
        exact ⟨_, rfl⟩
  | one =>
      simpa only [_root_.mul_one, _root_.one_mul, inv_mul_cancel] using
        InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup.one_mem
  | mul x y hx hy ihx ihy =>
      have hconj :
          swap01Aut⁻¹ * (x * y) * swap01Aut =
            (swap01Aut⁻¹ * x * swap01Aut) *
              (swap01Aut⁻¹ * y * swap01Aut) := by
        group
      have hmem :=
        InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup.mul_mem ihx ihy
      rw [hconj]
      exact hmem
  | inv x hx ihx =>
      have hconj :
          swap01Aut⁻¹ * x⁻¹ * swap01Aut =
            (swap01Aut⁻¹ * x * swap01Aut)⁻¹ := by
        group
      exact hconj ▸
        InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup.inv_mem ihx

/- CAS certificate: odd representative [0,1,0,0,1,0] satisfies s*r*s = r*s*r. -/
theorem swap01_rank_one_witness :
    let r : SplitOctF2Aut :=
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => false | 1 => true | 2 => false
        | 3 => false | 4 => true | 5 => false)
    swap01Aut * r * swap01Aut = r * swap01Aut * r := by
  dsimp
  apply automorphism_ext_of_basis
  intro i
  repeat rw [aut_mul_apply]
  repeat rw [pcWord_apply]
  fin_cases i <;>
    simp [pcWordFun, pcTermFun, swap01Aut_apply, swap01Fun,
      pc2Fun, pc5Fun,
      basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

/- CAS Gröbner certificate for the matrix rank-one representative
   `cartan * swap01 * cycle`; its Lean word is the reverse composition. -/
theorem cycle_swap01_cartan_conj_pc1 :
    let t : SplitOctF2Aut := cycle012Aut * (swap01Aut * swapCartanAut)
    t * pcGenerator 1 * t =
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => false | 1 => true | 2 => true
        | 3 => true | 4 => false | 5 => false) := by
  dsimp
  apply automorphism_ext_of_basis
  intro i
  repeat rw [aut_mul_apply]
  rw [pcWord_apply]
  fin_cases i <;>
    simp [pcWordFun, pcTermFun, pcGenerator, swap01Aut_apply, swap01Fun,
      cycle012Aut, cycle012Equiv, cycle012Fun,
      swapCartanAut, swapCartanEquiv, swapCartanFun,
      G2TwoSylowPCAutomorphisms.pc2Aut,
      G2TwoSylowPCAutomorphisms.pc2Equiv,
      G2TwoSylowPCGenerators.pc2Fun,
      pc3Fun, pc4Fun,
      basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

/- CAS Gröbner certificate: `t * pcGenerator 2 * t` has PC bits
   [0,1,1,1,1,1]. -/
theorem cycle_swap01_cartan_conj_pc2 :
    let t : SplitOctF2Aut := cycle012Aut * (swap01Aut * swapCartanAut)
    t * pcGenerator 2 * t =
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => false | 1 => true | 2 => true
        | 3 => true | 4 => true | 5 => true) := by
  dsimp
  apply automorphism_ext_of_basis
  intro i
  repeat rw [aut_mul_apply]
  rw [pcWord_apply]
  fin_cases i <;>
    simp [pcWordFun, pcTermFun, pcGenerator, swap01Aut_apply, swap01Fun,
      cycle012Aut, cycle012Equiv, cycle012Fun,
      swapCartanAut, swapCartanEquiv, swapCartanFun,
      G2TwoSylowPCAutomorphisms.pc3Aut,
      G2TwoSylowPCAutomorphisms.pc3Equiv,
      G2TwoSylowPCGenerators.pc3Fun,
      pc2Fun, pc4Fun, pc5Fun, pc6Fun,
      basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

/- CAS Gröbner certificate: `t * pcGenerator 3 * t` has PC bits
   [0,1,0,0,1,1]. -/
theorem cycle_swap01_cartan_conj_pc3 :
    let t : SplitOctF2Aut := cycle012Aut * (swap01Aut * swapCartanAut)
    t * pcGenerator 3 * t =
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => false | 1 => true | 2 => false
        | 3 => false | 4 => true | 5 => true) := by
  dsimp
  apply automorphism_ext_of_basis
  intro i
  repeat rw [aut_mul_apply]
  rw [pcWord_apply]
  fin_cases i <;>
    simp [pcWordFun, pcTermFun, pcGenerator, swap01Aut_apply, swap01Fun,
      cycle012Aut, cycle012Equiv, cycle012Fun,
      swapCartanAut, swapCartanEquiv, swapCartanFun,
      G2TwoSylowPCAutomorphisms.pc4Aut,
      G2TwoSylowPCAutomorphisms.involutiveEquiv,
      pc4Fun, pc2Fun, pc5Fun, pc6Fun,
      basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

/- CAS certificate: with t = s₁(swapCartan·cycle), the ordered PC witness is
   [1,0,0,1,0,0], and t r t = r t r. -/
theorem swap01_cartan_cycle_rank_one_witness :
    let t : SplitOctF2Aut := (swapCartanAut * cycle012Aut) * swap01Aut
    let r : SplitOctF2Aut :=
      G2TwoSylowSubgroup.pcWord (fun i => match i with
        | 0 => true | 1 => false | 2 => false
        | 3 => true | 4 => false | 5 => false)
    t * r * t = r * t * r := by
  dsimp
  apply automorphism_ext_of_basis
  intro i
  repeat rw [aut_mul_apply]
  repeat rw [pcWord_apply]
  fin_cases i <;>
    simp [pcWordFun, pcTermFun, swap01Aut_apply, swap01Fun,
      cycle012Aut, cycle012Equiv, cycle012Fun,
      swapCartanAut, swapCartanEquiv, swapCartanFun,
      pc1Fun, pc4Fun,
      basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

def swap01RankOneExponent : PCExponent := fun i => match i with
  | 0 => false | 1 => true | 2 => false
  | 3 => false | 4 => true | 5 => false

theorem swap01_borel_split (b : SplitOctF2Aut) (hb :
    b ∈ InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup) :
    b ∈ swap01ComplementSubgroup ∨
      ∃ h ∈ swap01ComplementSubgroup,
        b = G2TwoSylowSubgroup.pcWord swap01RankOneExponent * h := by
  rcases hb with ⟨e, rfl⟩
  by_cases he : e 1 = false
  · left
    exact pcWord_mem_swap01ComplementSubgroup e he
  · right
    have he' : e 1 = true := by
      cases h : e 1 with
      | false => exact False.elim (he h)
      | true => rfl
    let hExp : PCExponent :=
      InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.pcCombine
        (InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.pcInverse swap01RankOneExponent) e
    have hExp_one : hExp 1 = false := by
      change (InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.pcCombine
        (InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.pcInverse swap01RankOneExponent) e) 1 = false
      rw [InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.pcCombine_apply_one,
        InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm.pcInverse_apply_one, he']
      rfl
    refine ⟨G2TwoSylowSubgroup.pcWord hExp,
      pcWord_mem_swap01ComplementSubgroup hExp hExp_one, ?_⟩
    symm
    calc
      G2TwoSylowSubgroup.pcWord swap01RankOneExponent *
          G2TwoSylowSubgroup.pcWord hExp =
          G2TwoSylowSubgroup.pcWord (pcCombine swap01RankOneExponent hExp) := by
            rw [_root_.InfoGeometry.Algebra.Zorn.G2TwoPCConcreteCollector.pcWord_mul_pcWord]
      _ = G2TwoSylowSubgroup.pcWord e := by
        apply congrArg G2TwoSylowSubgroup.pcWord
        dsimp [hExp]
        group

theorem swap01_concrete_bn2 (b : SplitOctF2Aut)
    (hb : b ∈ InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup) :
    InfoGeometry.Algebra.Zorn.IndexTwoLevi.InBruhatCover
      InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup
      swap01Aut (swap01Aut * b * swap01Aut) := by
  let r : SplitOctF2Aut := G2TwoSylowSubgroup.pcWord swap01RankOneExponent
  have hr : r ∈ InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup := by
    exact ⟨swap01RankOneExponent, rfl⟩
  exact InfoGeometry.Algebra.Zorn.IndexTwoLevi.bn2_of_index2_split
    InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure.unipotentSubgroup
    swap01ComplementSubgroup swap01Aut swap01Aut_sq r hr
    (fun h hh => swap01_conj_complement_mem_unipotent h hh)
    (by simpa [r] using swap01_rank_one_witness) b hb
    (swap01_borel_split b hb)

end InfoGeometry.Algebra.Zorn.G2ConcreteBN2FirstConjugation

import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
import InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

set_option linter.unusedSimpArgs false

namespace InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
  (PCWordExp pcWordFun pcTermFun pcTerm_apply pcWord_apply)

/-- Peel step 0 using exact inverse pc1Aut⁻¹ = pc1Aut. -/
def peel0 (f : SplitOctF2Aut) : SplitOctF2Aut :=
  (if (f.1 (basis8 7)).x0 then pc1Aut else 1) * f

/-- Peel step 1 using the raw CAS pivot `M₁[3,2]` and the exact inverse
    `pc2Aut⁻¹ = pc6Aut * pc2Aut`.  This is deliberately a raw pivot, not
    `extractBit1`, since the latter itself performs the preceding peel. -/
def peel1 (f : SplitOctF2Aut) : SplitOctF2Aut :=
  (if (f.1 (basis8 2)).x1 then pc6Aut * pc2Aut else 1) * f

/-- Peel step 2 using exact inverse pc3Aut⁻¹ = pc6Aut * pc3Aut. -/
def peel2 (f : SplitOctF2Aut) : SplitOctF2Aut :=
  (if (f.1 (basis8 7)).x1 then pc6Aut * pc3Aut else 1) * f

/-- Peel step 4 and 3 using exact inverses pc5Aut and pc4Aut. -/
def peel34 (f : SplitOctF2Aut) : SplitOctF2Aut :=
  let e4 := (f.1 (basis8 2)).y1
  let e3 := (f.1 (basis8 3)).x2 ^^ e4
  (if e4 then pc5Aut else 1) * (if e3 then pc4Aut else 1) * f

/-- Peel step 5 using exact inverse pc6Aut⁻¹ = pc6Aut. -/
def peel5 (f : SplitOctF2Aut) : SplitOctF2Aut :=
  (if (f.1 (basis8 2)).x2 then pc6Aut else 1) * f

/-- Complete sequential peeling to identity. -/
def fullPeel (f : SplitOctF2Aut) : SplitOctF2Aut :=
  peel5 (peel34 (peel2 (peel1 (peel0 f))))

/-- Extraction of bit 0 from an automorphism. -/
def extractBit0 (f : SplitOctF2Aut) : Bool :=
  (f.1 (basis8 7)).x0

/-- Extraction of bit 1 after peeling bit 0. -/
def extractBit1 (f : SplitOctF2Aut) : Bool :=
  ((peel0 f).1 (basis8 2)).x1

/-- Extraction of bit 2 after peeling bits 0 and 1. -/
def extractBit2 (f : SplitOctF2Aut) : Bool :=
  ((peel1 (peel0 f)).1 (basis8 7)).x1

/-- Extraction of bit 4 after peeling bits 0, 1, and 2. -/
def extractBit4 (f : SplitOctF2Aut) : Bool :=
  ((peel2 (peel1 (peel0 f))).1 (basis8 2)).y1

/-- Extraction of bit 3 after peeling bits 0, 1, and 2. -/
def extractBit3 (f : SplitOctF2Aut) : Bool :=
  let f3 := peel2 (peel1 (peel0 f))
  (f3.1 (basis8 3)).x2 ^^ (f3.1 (basis8 2)).y1

/-- Extraction of bit 5 after peeling bits 0, 1, 2, 3, and 4. -/
def extractBit5 (f : SplitOctF2Aut) : Bool :=
  ((peel34 (peel2 (peel1 (peel0 f)))).1 (basis8 2)).x2

/-- Bundled 6-bit recovery map from sequential peeling. -/
def extractAllBits (f : SplitOctF2Aut) : Fin 6 → Bool
  | 0 => extractBit0 f
  | 1 => extractBit1 f
  | 2 => extractBit2 f
  | 3 => extractBit3 f
  | 4 => extractBit4 f
  | 5 => extractBit5 f

lemma pcTermFun_x0 (i : Fin 6) (b : Bool) (X : SplitOctF2) :
    (pcTermFun i b X).x0 =
      if i = 0 then (if b then X.x0 ^^ X.y2 else X.x0) else X.x0 := by
  cases b <;> fin_cases i <;> rfl

lemma pcTermFun_y2 (i : Fin 6) (b : Bool) (X : SplitOctF2) :
    (pcTermFun i b X).y2 = X.y2 := by
  cases b <;> fin_cases i <;> rfl

lemma pcTermFun_x1 (i : Fin 6) (b : Bool) (X : SplitOctF2) :
    (pcTermFun i b X).x1 =
      if i = 1 then (if b then X.x0 ^^ X.x1 else X.x1)
      else if i = 2 then (if b then X.x1 ^^ X.y2 else X.x1)
      else X.x1 := by
  cases b <;> fin_cases i <;> rfl

lemma pcTermFun_y1 (i : Fin 6) (b : Bool) (X : SplitOctF2) :
    (pcTermFun i b X).y1 =
      if i = 0 then (if b then X.a ^^ X.b ^^ X.x1 ^^ X.y1 ^^ X.y2 else X.y1)
      else if i = 1 then (if b then X.x0 ^^ X.y1 ^^ X.y2 else X.y1)
      else if i = 2 then (if b then X.x0 ^^ X.y1 ^^ X.y2 else X.y1)
      else if i = 3 then (if b then X.y1 ^^ X.y2 else X.y1)
      else if i = 4 then (if b then X.x0 ^^ X.y1 ^^ X.y2 else X.y1)
      else X.y1 := by
  cases b <;> fin_cases i <;> rfl

lemma pcTermFun_basis8_4_y1 (i : Fin 6) (b : Bool) :
    (pcTermFun i b (basis8 4)).y1 = false := by
  cases b <;> fin_cases i <;> rfl

lemma pcTermFun_basis8_6_y1 (i : Fin 6) (b : Bool) :
    (pcTermFun i b (basis8 6)).y1 = true := by
  cases b <;> fin_cases i <;> rfl

lemma pcWordFun_x0_transport (e : PCWordExp) (X : SplitOctF2) :
    (pcWordFun e X).x0 =
      if e 0 then X.x0 ^^ X.y2 else X.x0 := by
  simp [pcWordFun, pcTermFun_x0]

lemma pcWordFun_x1_transport (e : PCWordExp) (X : SplitOctF2) :
    (pcWordFun e X).x1 =
      let x0' := if e 0 then X.x0 ^^ X.y2 else X.x0
      let x1' := if e 1 then x0' ^^ X.x1 else X.x1
      if e 2 then x1' ^^ X.y2 else x1' := by
  simp [pcWordFun, pcTermFun_x0, pcTermFun_x1, pcTermFun_y2]

lemma automorphism_mul_apply (g h : SplitOctF2Aut) (X : SplitOctF2) :
    (g * h).1 X = h.1 (g.1 X) := rfl

lemma automorphism_map_add (g : SplitOctF2Aut) (X Y : SplitOctF2) :
    g.1 (add X Y) = add (g.1 X) (g.1 Y) := g.2.2.1 X Y

lemma pcWord_map_add (e : PCWordExp) (X Y : SplitOctF2) :
    (G2TwoSylowSubgroup.pcWord e).1 (add X Y) =
      add ((G2TwoSylowSubgroup.pcWord e).1 X)
        ((G2TwoSylowSubgroup.pcWord e).1 Y) := by
  exact (G2TwoSylowSubgroup.pcWord e).2.2.1 X Y

lemma pcWord_map_mul (e : PCWordExp) (X Y : SplitOctF2) :
    (G2TwoSylowSubgroup.pcWord e).1 (mul X Y) =
      mul ((G2TwoSylowSubgroup.pcWord e).1 X)
        ((G2TwoSylowSubgroup.pcWord e).1 Y) := by
  exact (G2TwoSylowSubgroup.pcWord e).2.2.2 X Y

lemma pc1Aut_basis8_2 : pc1Aut.1 (basis8 2) = basis8 2 := by
  rfl

lemma pc1Aut_basis8_4 :
    pc1Aut.1 (basis8 4) = basis8 4 := by
  change G2TwoSylowPCGenerators.pc1Fun (basis8 4) = _
  ext <;> simp [G2TwoSylowPCGenerators.pc1Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma pc1Aut_basis8_6 :
    pc1Aut.1 (basis8 6) = basis8 6 := by
  change G2TwoSylowPCGenerators.pc1Fun (basis8 6) = _
  ext <;> simp [G2TwoSylowPCGenerators.pc1Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma peel0_apply_basis8_4 (f : SplitOctF2Aut) :
    (peel0 f).1 (basis8 4) = f.1 (basis8 4) := by
  dsimp [peel0]
  split
  · rw [automorphism_mul_apply, pc1Aut_basis8_4]
  · simp

lemma peel0_apply_basis8_6 (f : SplitOctF2Aut) :
    (peel0 f).1 (basis8 6) = f.1 (basis8 6) := by
  dsimp [peel0]
  split
  · rw [automorphism_mul_apply, pc1Aut_basis8_6]
  · simp

lemma pc1Aut_basis8_7 :
    pc1Aut.1 (basis8 7) = add (basis8 2) (add (basis8 6) (basis8 7)) := by
  ext <;> rfl

lemma pc6pc2Aut_basis8_7 :
    (pc6Aut * pc2Aut).1 (basis8 7) =
      add ePlus (add eMinus (add (basis8 4)
        (add (basis8 6) (basis8 7)))) := by
  change G2TwoSylowPCGenerators.pc2Fun
    (G2TwoSylowPCGenerators.pc6Fun (basis8 7)) = _
  ext <;> simp [G2TwoSylowPCGenerators.pc2Fun,
    G2TwoSylowPCGenerators.pc6Fun, basis8, ePlus, eMinus, up0, up1, up2,
    down0, down1, down2, add, add2, Bool.xor_comm]

theorem extractBit0_pcWord (e : PCWordExp) :
    extractBit0 (G2TwoSylowSubgroup.pcWord e) = e 0 := by
  change ((G2TwoSylowSubgroup.pcWord e).1 (basis8 7)).x0 = e 0
  rw [pcWord_apply]
  rw [pcWordFun_x0_transport]
  simp [basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

lemma pcWordFun_x1_basis8_2 (e : PCWordExp) :
    (pcWordFun e (basis8 2)).x1 = e 1 := by
  rw [pcWordFun_x1_transport]
  simp [basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

lemma pcWordFun_x1_basis8_7_raw (e : PCWordExp) :
    (pcWordFun e (basis8 7)).x1 =
      if e 2 then (!e 1 || !e 0) else (e 1 && e 0) := by
  rw [pcWordFun_x1_transport]
  simp [basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2,
    Bool.xor_comm]

lemma pcWordFun_x0_basis8_6 (e : PCWordExp) :
    (pcWordFun e (basis8 6)).x0 = false := by
  change
    (pcTermFun 5 (e 5) (pcTermFun 4 (e 4)
      (pcTermFun 3 (e 3) (pcTermFun 2 (e 2)
        (pcTermFun 1 (e 1) (pcTermFun 0 (e 0) (basis8 6))))))).x0 = false
  simp [pcTermFun_x0, basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

lemma pcWordFun_x0_basis8_2 (e : PCWordExp) :
    (pcWordFun e (basis8 2)).x0 = true := by
  change
    (pcTermFun 5 (e 5) (pcTermFun 4 (e 4)
      (pcTermFun 3 (e 3) (pcTermFun 2 (e 2)
        (pcTermFun 1 (e 1) (pcTermFun 0 (e 0) (basis8 2))))))).x0 = true
  simp [pcTermFun_x0, basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

lemma pcWordFun_x0_basis8_7 (e : PCWordExp) :
    (pcWordFun e (basis8 7)).x0 = e 0 := by
  change
    (pcTermFun 5 (e 5) (pcTermFun 4 (e 4)
      (pcTermFun 3 (e 3) (pcTermFun 2 (e 2)
        (pcTermFun 1 (e 1) (pcTermFun 0 (e 0) (basis8 7))))))).x0 = e 0
  simp [pcTermFun_x0, basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

lemma pcWordFun_x1_basis8_6 (e : PCWordExp) :
    (pcWordFun e (basis8 6)).x1 = false := by
  change
    (pcTermFun 5 (e 5) (pcTermFun 4 (e 4)
      (pcTermFun 3 (e 3) (pcTermFun 2 (e 2)
        (pcTermFun 1 (e 1) (pcTermFun 0 (e 0) (basis8 6))))))).x1 = false
  simp [pcTermFun_x0, pcTermFun_y2, pcTermFun_x1, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

lemma pcWordFun_x1_basis8_4 (e : PCWordExp) :
    (pcWordFun e (basis8 4)).x1 = false := by
  change
    (pcTermFun 5 (e 5) (pcTermFun 4 (e 4)
      (pcTermFun 3 (e 3) (pcTermFun 2 (e 2)
        (pcTermFun 1 (e 1) (pcTermFun 0 (e 0) (basis8 4))))))).x1 = false
  simp [pcTermFun_x0, pcTermFun_y2, pcTermFun_x1, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

theorem extractBit1_pcWord (e : PCWordExp) :
    extractBit1 (G2TwoSylowSubgroup.pcWord e) = e 1 := by
  change ((peel0 (G2TwoSylowSubgroup.pcWord e)).1 (basis8 2)).x1 = e 1
  change (((if extractBit0 (G2TwoSylowSubgroup.pcWord e) then pc1Aut else 1) *
    G2TwoSylowSubgroup.pcWord e).1 (basis8 2)).x1 = e 1
  rw [automorphism_mul_apply]
  split_ifs
  · rw [pc1Aut_basis8_2, pcWord_apply]
    exact pcWordFun_x1_basis8_2 e
  · rw [pcWord_apply]
    exact pcWordFun_x1_basis8_2 e

lemma peel0_pcWord_basis8_2 (e : PCWordExp) :
    (peel0 (G2TwoSylowSubgroup.pcWord e)).1 (basis8 2) =
      (G2TwoSylowSubgroup.pcWord e).1 (basis8 2) := by
  change (((if extractBit0 (G2TwoSylowSubgroup.pcWord e) then pc1Aut else 1) *
    G2TwoSylowSubgroup.pcWord e).1 (basis8 2) = _)
  rw [automorphism_mul_apply]
  split_ifs
  · rw [pc1Aut_basis8_2]
  · rfl

lemma peel0_apply_basis8_7 (f : SplitOctF2Aut) :
    (peel0 f).1 (basis8 7) =
      if extractBit0 f then f.1 (add (basis8 2) (add (basis8 6) (basis8 7)))
      else f.1 (basis8 7) := by
  change (((if extractBit0 f then pc1Aut else 1) * f).1 (basis8 7)) = _
  rw [automorphism_mul_apply]
  split_ifs
  · rw [pc1Aut_basis8_7]
  · rfl

lemma pcWord_apply_cartan_mix (e : PCWordExp) :
    (G2TwoSylowSubgroup.pcWord e).1
        (add (basis8 2) (add (basis8 6) (basis8 7))) =
      add ((G2TwoSylowSubgroup.pcWord e).1 (basis8 2))
        (add ((G2TwoSylowSubgroup.pcWord e).1 (basis8 6))
          ((G2TwoSylowSubgroup.pcWord e).1 (basis8 7))) := by
  rw [pcWord_map_add, pcWord_map_add]

lemma peel0_pcWord_basis8_7_x0 (e : PCWordExp) :
    ((peel0 (G2TwoSylowSubgroup.pcWord e)).1 (basis8 7)).x0 = false := by
  rw [peel0_apply_basis8_7, extractBit0_pcWord]
  by_cases h0 : e 0
  · simp only [if_pos h0]
    rw [pcWord_apply_cartan_mix]
    rw [pcWord_apply, pcWord_apply, pcWord_apply]
    simp [pcWordFun_x0_basis8_2, pcWordFun_x0_basis8_6,
      pcWordFun_x0_basis8_7, add, add2, h0]
  · simp only [if_neg h0]
    rw [pcWord_apply]
    simpa [h0] using pcWordFun_x0_basis8_7 e

lemma peel0_pcWord_basis8_7_x1 (e : PCWordExp) :
    ((peel0 (G2TwoSylowSubgroup.pcWord e)).1 (basis8 7)).x1 = e 2 := by
  rw [peel0_apply_basis8_7, extractBit0_pcWord]
  by_cases h0 : e 0
  · simp only [if_pos h0]
    rw [pcWord_apply_cartan_mix]
    rw [pcWord_apply, pcWord_apply, pcWord_apply]
    simp [pcWordFun_x1_basis8_2, pcWordFun_x1_basis8_6,
      pcWordFun_x1_basis8_7_raw, add, add2, h0]
    grind
  · simp only [if_neg h0]
    rw [pcWord_apply]
    rw [pcWordFun_x1_basis8_7_raw]
    simp [h0]

def makeExp (b0 b1 b2 b3 b4 b5 : Bool) : PCWordExp
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | 5 => b5

lemma pcWordExp_eq_makeExp (e : PCWordExp) :
    e = makeExp (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) := by
  funext i
  fin_cases i <;> rfl

theorem extractBit3_pcWord (e : PCWordExp) :
    extractBit3 (G2TwoSylowSubgroup.pcWord e) = e 3 := by
  have he : e = makeExp (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) := pcWordExp_eq_makeExp e
  rw [he]
  cases (e 0) <;> cases (e 1) <;> cases (e 2) <;> cases (e 3) <;> cases (e 4) <;> cases (e 5) <;> rfl

theorem extractBit4_pcWord (e : PCWordExp) :
    extractBit4 (G2TwoSylowSubgroup.pcWord e) = e 4 := by
  have he : e = makeExp (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) := pcWordExp_eq_makeExp e
  rw [he]
  cases (e 0) <;> cases (e 1) <;> cases (e 2) <;> cases (e 3) <;> cases (e 4) <;> cases (e 5) <;> rfl

theorem extractBit5_pcWord (e : PCWordExp) :
    extractBit5 (G2TwoSylowSubgroup.pcWord e) = e 5 := by
  have he : e = makeExp (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) := pcWordExp_eq_makeExp e
  rw [he]
  cases (e 0) <;> cases (e 1) <;> cases (e 2) <;> cases (e 3) <;> cases (e 4) <;> cases (e 5) <;> rfl


theorem extractBit2_pcWord (e : PCWordExp) :
    extractBit2 (G2TwoSylowSubgroup.pcWord e) = e 2 := by
  change ((peel1 (peel0 (G2TwoSylowSubgroup.pcWord e))).1
    (basis8 7)).x1 = e 2
  change (((if ((peel0 (G2TwoSylowSubgroup.pcWord e)).1
      (basis8 2)).x1 then pc6Aut * pc2Aut else 1) *
      peel0 (G2TwoSylowSubgroup.pcWord e)).1 (basis8 7)).x1 = e 2
  change (((if extractBit1 (G2TwoSylowSubgroup.pcWord e) then
      pc6Aut * pc2Aut else 1) * peel0 (G2TwoSylowSubgroup.pcWord e)).1
      (basis8 7)).x1 = e 2
  rw [extractBit1_pcWord]
  split_ifs
  · rw [automorphism_mul_apply, pc6pc2Aut_basis8_7]
    rw [← add_assoc, ePlus_add_eMinus_eq_one]
    rw [automorphism_map_add, (peel0 (G2TwoSylowSubgroup.pcWord e)).2.1,
      automorphism_map_add, automorphism_map_add]
    rw [peel0_apply_basis8_4, peel0_apply_basis8_6]
    simp [pcWord_apply, pcWordFun_x1_basis8_4,
      pcWordFun_x1_basis8_6, peel0_pcWord_basis8_7_x1,
      add, add2, one]
  · rw [automorphism_mul_apply]
    exact peel0_pcWord_basis8_7_x1 e

theorem extractAllBits_pcWord (e : PCWordExp) :
    extractAllBits (G2TwoSylowSubgroup.pcWord e) = e := by
  funext k
  fin_cases k
  · exact extractBit0_pcWord e
  · exact extractBit1_pcWord e
  · exact extractBit2_pcWord e
  · exact extractBit3_pcWord e
  · exact extractBit4_pcWord e
  · exact extractBit5_pcWord e

theorem pcWord_injective :
    Function.Injective G2TwoSylowSubgroup.pcWord := by
  intro e f h
  have hrec : extractAllBits (G2TwoSylowSubgroup.pcWord e) =
              extractAllBits (G2TwoSylowSubgroup.pcWord f) := by
    rw [h]
  rw [extractAllBits_pcWord, extractAllBits_pcWord] at hrec
  exact hrec

theorem pcWord_range_card :
    Nat.card (Set.range G2TwoSylowSubgroup.pcWord) = 64 := by
  rw [Nat.card_range_of_injective pcWord_injective]
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  norm_num

theorem sylowTwoSubgroup_card_ge_64 :
    64 ≤ Nat.card G2TwoSylowSubgroup.sylowTwoSubgroup := by
  let f : PCWordExp →
      {x : SplitOctF2Aut // x ∈ G2TwoSylowSubgroup.sylowTwoSubgroup} := fun e =>
    ⟨G2TwoSylowSubgroup.pcWord e, G2TwoSylowSubgroup.pcWord_mem_sylow e⟩
  have hf : Function.Injective f := by
    intro e g h
    apply pcWord_injective
    exact congrArg Subtype.val h
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card,
    G2TwoSylowSubgroup.pcWordExp_card] at hc
  exact hc

end InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

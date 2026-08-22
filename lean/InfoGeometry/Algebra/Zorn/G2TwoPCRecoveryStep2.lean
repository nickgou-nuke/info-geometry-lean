import InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

namespace InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep2

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2TwoBooleanNormalizer
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup (PCWordExp pcWord_apply)

lemma automorphism_mul_apply_local (g h : SplitOctF2Aut) (X : SplitOctF2) :
    (g * h).1 X = h.1 (g.1 X) := rfl

lemma automorphism_map_add_y1 (g : SplitOctF2Aut) (X Y : SplitOctF2) :
    (g.1 (add X Y)).y1 = add2 (g.1 X).y1 (g.1 Y).y1 := by
  rw [automorphism_map_add]
  rfl

lemma automorphism_map_add5_y1 (g : SplitOctF2Aut)
    (X₀ X₁ X₂ X₃ X₄ : SplitOctF2) :
    (g.1 (add X₀ (add X₁ (add X₂ (add X₃ X₄))))).y1 =
      add2 (g.1 X₀).y1
        (add2 (g.1 X₁).y1
          (add2 (g.1 X₂).y1
            (add2 (g.1 X₃).y1 (g.1 X₄).y1))) := by
  rw [automorphism_map_add_y1, automorphism_map_add_y1,
    automorphism_map_add_y1, automorphism_map_add_y1]

lemma automorphism_map_add2_y1 (g : SplitOctF2Aut)
    (X Y : SplitOctF2) :
    (g.1 (add X Y)).y1 = add2 (g.1 X).y1 (g.1 Y).y1 :=
  automorphism_map_add_y1 g X Y

lemma automorphism_map_add3_y1 (g : SplitOctF2Aut)
    (X Y Z : SplitOctF2) :
    (g.1 (add X (add Y Z))).y1 =
      add2 (g.1 X).y1 (add2 (g.1 Y).y1 (g.1 Z).y1) := by
  rw [automorphism_map_add_y1, automorphism_map_add_y1]

lemma pc6pc2_basis8_7 :
    (G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut).1 (basis8 7) =
      add ePlus (add eMinus (add (basis8 4)
        (add (basis8 6) (basis8 7)))) := by
  change pc2Fun (pc6Fun (basis8 7)) = _
  ext <;> dsimp [add, add2]
  all_goals simp [pc2Fun, pc6Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

lemma pc6pc2_basis8_7_x1 :
    ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut).1 (basis8 7)).x1 = false := by
  rw [pc6pc2_basis8_7]
  simp [basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma pc6pc2_apply_x1 (X : SplitOctF2) :
    ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut).1 X).x1 = (X.x0 ^^ X.x1) := by
  change (pc2Fun (pc6Fun X)).x1 = (X.x0 ^^ X.x1)
  simp [pc2Fun, pc6Fun]

lemma pc6pc2_apply_y1 (X : SplitOctF2) :
    ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut).1 X).y1 =
      (X.x0 ^^ X.y1 ^^ X.y2) := by
  change (pc2Fun (pc6Fun X)).y1 = (X.x0 ^^ X.y1 ^^ X.y2)
  rfl

lemma pc6pc2_basis8_2 :
    (G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut).1 (basis8 2) =
      add (basis8 2) (add (basis8 3)
        (add (basis8 4) (add (basis8 5) (basis8 6)))) := by
  change pc2Fun (pc6Fun (basis8 2)) = _
  ext <;> simp [pc2Fun, pc6Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma pc6pc2_basis8_3 :
    (G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut).1 (basis8 3) =
      add (basis8 3) (add (basis8 4) (basis8 5)) := by
  change pc2Fun (pc6Fun (basis8 3)) = _
  ext <;> simp [pc2Fun, pc6Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma pc6pc2_basis8_4 :
    (G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut).1 (basis8 4) = basis8 4 := by
  change pc2Fun (pc6Fun (basis8 4)) = _
  ext <;> simp [pc2Fun, pc6Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma pc6pc2_basis8_5 :
    (G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut).1 (basis8 5) = basis8 5 := by
  change pc2Fun (pc6Fun (basis8 5)) = _
  ext <;> simp [pc2Fun, pc6Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma pc6pc2_basis8_6 :
    (G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut).1 (basis8 6) =
      add (basis8 5) (basis8 6) := by
  change pc2Fun (pc6Fun (basis8 6)) = _
  ext <;> simp [pc2Fun, pc6Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma peel1_basis8_2 (f : SplitOctF2Aut) :
    (peel1 f).1 (basis8 2) =
      if (f.1 (basis8 2)).x1 then
        f.1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
          G2TwoSylowPCAutomorphisms.pc2Aut).1 (basis8 2))
      else f.1 (basis8 2) := by
  dsimp [peel1]
  split
  · rw [automorphism_mul_apply_local]
  · simp

lemma peel1_basis8_2_y1 (f : SplitOctF2Aut) :
    ((peel1 f).1 (basis8 2)).y1 =
      if (f.1 (basis8 2)).x1 then
        (f.1 (add (basis8 2) (add (basis8 3)
          (add (basis8 4) (add (basis8 5) (basis8 6)))))).y1
      else (f.1 (basis8 2)).y1 := by
  rw [peel1_basis8_2]
  split
  · rw [pc6pc2_basis8_2]
  · rfl

lemma peel1_basis8 (f : SplitOctF2Aut) (k : Fin 8) :
    (peel1 f).1 (basis8 k) =
      if (f.1 (basis8 2)).x1 then
        f.1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
          G2TwoSylowPCAutomorphisms.pc2Aut).1 (basis8 k))
      else f.1 (basis8 k) := by
  dsimp [peel1]
  split
  · rw [automorphism_mul_apply_local]
  · simp

lemma peel1_sum_basis_y1 (f : SplitOctF2Aut) :
    ((peel1 f).1
      (add (basis8 2) (add (basis8 3)
        (add (basis8 4) (add (basis8 5) (basis8 6)))))).y1 =
      if (f.1 (basis8 2)).x1 then
        (f.1 (add (basis8 2) (basis8 4))).y1
      else (f.1
        (add (basis8 2) (add (basis8 3)
          (add (basis8 4) (add (basis8 5) (basis8 6)))))).y1 := by
  rw [automorphism_map_add5_y1 (peel1 f)
    (basis8 2) (basis8 3) (basis8 4) (basis8 5) (basis8 6)]
  rw [automorphism_map_add5_y1 f
    (basis8 2) (basis8 3) (basis8 4) (basis8 5) (basis8 6)]
  rw [peel1_basis8, peel1_basis8, peel1_basis8, peel1_basis8, peel1_basis8]
  split
  · rw [pc6pc2_basis8_2, pc6pc2_basis8_3, pc6pc2_basis8_4,
      pc6pc2_basis8_5, pc6pc2_basis8_6]
    rw [automorphism_map_add3_y1, automorphism_map_add2_y1,
      automorphism_map_add2_y1, automorphism_map_add2_y1]
    rw [automorphism_map_add_y1 f (basis8 4) (basis8 5)]
    rw [automorphism_map_add_y1 f (basis8 2) (basis8 4)]
    rw [← bitToF2_eq_iff]
    simp only [add2, bitToF2_xor]
    ring_nf <;> simp [F2_mul_two, F2_mul_three, F2_mul_four]
  · rfl

lemma extractBit2_pcWord (e : PCWordExp) :
    extractBit2 (G2TwoSylowSubgroup.pcWord e) = e 2 := by
  change ((peel1 (peel0 (G2TwoSylowSubgroup.pcWord e))).1
    (basis8 7)).x1 = e 2
  change (((if ((peel0 (G2TwoSylowSubgroup.pcWord e)).1
      (basis8 2)).x1 then
      G2TwoSylowPCAutomorphisms.pc6Aut *
        G2TwoSylowPCAutomorphisms.pc2Aut else 1) *
      peel0 (G2TwoSylowSubgroup.pcWord e)).1 (basis8 7)).x1 = e 2
  change (((if extractBit1 (G2TwoSylowSubgroup.pcWord e) then
      G2TwoSylowPCAutomorphisms.pc6Aut *
        G2TwoSylowPCAutomorphisms.pc2Aut else 1) *
      peel0 (G2TwoSylowSubgroup.pcWord e)).1 (basis8 7)).x1 = e 2
  rw [extractBit1_pcWord]
  split_ifs
  · rw [automorphism_mul_apply_local, pc6pc2_basis8_7]
    rw [← add_assoc, ePlus_add_eMinus_eq_one]
    rw [automorphism_map_add, (peel0 (G2TwoSylowSubgroup.pcWord e)).2.1,
      automorphism_map_add,
      automorphism_map_add]
    rw [peel0_apply_basis8_4, peel0_apply_basis8_6]
    simp [pcWord_apply, pcWordFun_x1_basis8_4,
      pcWordFun_x1_basis8_6,
      InfoGeometry.Algebra.Zorn.G2TwoPCRecovery.peel0_pcWord_basis8_7_x1,
      add, add2, one]
  · rw [automorphism_mul_apply_local]
    exact InfoGeometry.Algebra.Zorn.G2TwoPCRecovery.peel0_pcWord_basis8_7_x1 e


lemma pcTermFun_x1_local (i : Fin 6) (b : Bool) (X : SplitOctF2) :
    (G2TwoSylowSubgroup.pcTermFun i b X).x1 =
      if i = 1 then (if b then X.x0 ^^ X.x1 else X.x1)
      else if i = 2 then (if b then X.x1 ^^ X.y2 else X.x1)
      else X.x1 := by
  cases b <;> fin_cases i <;> rfl

lemma pcTermFun_x0_local (i : Fin 6) (b : Bool) (X : SplitOctF2) :
    (G2TwoSylowSubgroup.pcTermFun i b X).x0 =
      if i = 0 then (if b then X.x0 ^^ X.y2 else X.x0) else X.x0 := by
  cases b <;> fin_cases i <;> rfl

lemma pcTermFun_y2_local (i : Fin 6) (b : Bool) (X : SplitOctF2) :
    (G2TwoSylowSubgroup.pcTermFun i b X).y2 = X.y2 := by
  cases b <;> fin_cases i <;> rfl

/-- THEOREM (Exact 6-Bit Recovery from Peeling):
Every 6-bit polycyclic word `pcWord e` has its full exponent tuple `e`
faithfully recovered by sequential peeling on concrete basis elements:
  `extractAllBits (pcWord e) = e`
-/
theorem extractAllBits_pcWord (e : PCWordExp) :
    extractAllBits (G2TwoSylowSubgroup.pcWord e) = e := by
  funext i
  fin_cases i
  · exact extractBit0_pcWord e
  · exact extractBit1_pcWord e
  · exact extractBit2_pcWord e
  · exact InfoGeometry.Algebra.Zorn.G2TwoPCRecovery.extractBit3_pcWord e
  · exact InfoGeometry.Algebra.Zorn.G2TwoPCRecovery.extractBit4_pcWord e
  · exact InfoGeometry.Algebra.Zorn.G2TwoPCRecovery.extractBit5_pcWord e

/-- MAIN THEOREM (Injectivity of the G₂(2) Polycyclic Word Map):
The 6-bit normal form parameterization `pcWord : Fin 6 → Bool → G₂(2)`
is strictly injective:
  `pcWord e = pcWord f ⟹ e = f`
-/
theorem pcWord_injective : Function.Injective G2TwoSylowSubgroup.pcWord := by
  intro e1 e2 h
  have h_ext := congr_arg extractAllBits h
  rw [extractAllBits_pcWord, extractAllBits_pcWord] at h_ext
  exact h_ext

end InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep2

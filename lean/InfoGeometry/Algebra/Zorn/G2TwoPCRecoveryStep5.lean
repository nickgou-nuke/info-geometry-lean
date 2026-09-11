import InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep4

namespace InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep5

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep4

lemma mul_apply (g h : SplitOctF2Aut) (X : SplitOctF2) :
    (g * h).1 X = h.1 (g.1 X) := rfl

lemma pc4_basis8_2 :
    G2TwoSylowPCAutomorphisms.pc4Aut.1 (basis8 2) = basis8 2 := by
  change pc4Fun (basis8 2) = _
  ext <;> simp [pc4Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

lemma pc4_basis8_4 :
    G2TwoSylowPCAutomorphisms.pc4Aut.1 (basis8 4) = basis8 4 := by
  change pc4Fun (basis8 4) = _
  ext <;> simp [pc4Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

lemma pc5_basis8_4 :
    G2TwoSylowPCAutomorphisms.pc5Aut.1 (basis8 4) = basis8 4 := by
  change pc5Fun (basis8 4) = _
  ext <;> simp [pc5Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

lemma pc5pc4_basis8_4 :
    (G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc4Aut).1 (basis8 4) = basis8 4 := by
  change pc4Fun (pc5Fun (basis8 4)) = _
  ext <;> simp [pc4Fun, pc5Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

lemma peel34_basis8_4 (f : SplitOctF2Aut) :
    (peel34 f).1 (basis8 4) = f.1 (basis8 4) := by
  dsimp [peel34]
  split <;> split
  · change f.1 (pc4Fun (pc5Fun (basis8 4))) = _
    congr 1
  · change f.1 (pc5Fun (basis8 4)) = _
    congr 1
  · change f.1 (pc4Fun (basis8 4)) = _
    congr 1
  · simp

lemma peel34_preceding_basis8_4_fixed (f : SplitOctF2Aut) :
    (peel34 (peel2 (peel1 (peel0 f)))).1 (basis8 4) =
      f.1 (basis8 4) := by
  rw [peel34_basis8_4]
  exact peel2_peel1_peel0_basis8_4_fixed f

/-! The final CAS peel uses the involution `pc6Aut`; on the pivot
coordinate vector `x₀` it adds the `x₂` basis direction. -/
lemma pc6_basis8_2 :
    G2TwoSylowPCAutomorphisms.pc6Aut.1 (basis8 2) =
      add (basis8 2) (basis8 4) := by
  change pc6Fun (basis8 2) = _
  ext <;> simp [pc6Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma pc6_basis8_4 :
    G2TwoSylowPCAutomorphisms.pc6Aut.1 (basis8 4) = basis8 4 := by
  change pc6Fun (basis8 4) = _
  ext <;> simp [pc6Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

lemma peel5_basis8_4 (f : SplitOctF2Aut) :
    (peel5 f).1 (basis8 4) = f.1 (basis8 4) := by
  dsimp [peel5]
  split
  · rw [mul_apply, pc6_basis8_4]
  · rfl

lemma pc4_basis8_5 :
    G2TwoSylowPCAutomorphisms.pc4Aut.1 (basis8 5) = basis8 5 := by
  ext <;> rfl

lemma pc5_basis8_5 :
    G2TwoSylowPCAutomorphisms.pc5Aut.1 (basis8 5) = basis8 5 := by
  ext <;> rfl

lemma pc6_basis8_5 :
    G2TwoSylowPCAutomorphisms.pc6Aut.1 (basis8 5) = basis8 5 := by
  ext <;> rfl

lemma peel34_basis8_5 (f : SplitOctF2Aut) :
    (peel34 f).1 (basis8 5) = f.1 (basis8 5) := by
  dsimp [peel34]
  split <;> split
  · change f.1 (pc4Fun (pc5Fun (basis8 5))) = _
    congr 1
  · change f.1 (pc5Fun (basis8 5)) = _
    congr 1
  · change f.1 (pc4Fun (basis8 5)) = _
    congr 1
  · simp

lemma peel5_basis8_5 (f : SplitOctF2Aut) :
    (peel5 f).1 (basis8 5) = f.1 (basis8 5) := by
  dsimp [peel5]
  split
  · rw [mul_apply, pc6_basis8_5]
  · rfl

lemma fullPeel_basis8_5_eq_peel0 (f : SplitOctF2Aut) :
    (fullPeel f).1 (basis8 5) = (peel0 f).1 (basis8 5) := by
  unfold fullPeel
  rw [peel5_basis8_5, peel34_basis8_5, peel2_peel1_peel0_basis8_5_eq_peel0]

lemma pc6_basis8_2_x2 :
    (G2TwoSylowPCAutomorphisms.pc6Aut.1 (basis8 2)).x2 = true := by
  rw [pc6_basis8_2]
  simp [basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma pc6_apply_x2 (X : SplitOctF2) :
    (G2TwoSylowPCAutomorphisms.pc6Aut.1 X).x2 = (X.x0 ^^ X.x2) := by
  change (pc6Fun X).x2 = _
  rfl

lemma pc6_apply_x0 (X : SplitOctF2) :
    (G2TwoSylowPCAutomorphisms.pc6Aut.1 X).x0 = X.x0 := by
  change (pc6Fun X).x0 = _
  rfl

lemma pc6_apply_x1 (X : SplitOctF2) :
    (G2TwoSylowPCAutomorphisms.pc6Aut.1 X).x1 = X.x1 := by
  change (pc6Fun X).x1 = _
  rfl

lemma peel5_basis8_2 (f : SplitOctF2Aut) :
    (peel5 f).1 (basis8 2) =
      if (f.1 (basis8 2)).x2 then
        f.1 (add (basis8 2) (basis8 4))
      else f.1 (basis8 2) := by
  dsimp [peel5]
  split
  · rw [mul_apply, pc6_basis8_2]
  · simp

lemma peel5_basis8_2_x2 (f : SplitOctF2Aut) :
    ((peel5 f).1 (basis8 2)).x2 =
      if (f.1 (basis8 2)).x2 then
        (f.1 (add (basis8 2) (basis8 4))).x2
      else (f.1 (basis8 2)).x2 := by
  rw [peel5_basis8_2]
  split <;> rfl

lemma peel5_basis8_2_x2_of_basis8_4_fixed
    {f : SplitOctF2Aut}
    (h4 : f.1 (basis8 4) = basis8 4) :
    ((peel5 f).1 (basis8 2)).x2 = false := by
  rw [peel5_basis8_2_x2]
  split
  · next hx2 =>
    rw [f.2.2.1, h4]
    have hx4 : (f.1 (basis8 4)).x2 = true := by
      rw [h4]
      rfl
    simpa [add, hx4, basis8] using hx2
  · next hx2 =>
    cases h : (f.1 (basis8 2)).x2
    · rfl
    · contradiction

lemma peel5_basis8_2_x0 (f : SplitOctF2Aut) :
    ((peel5 f).1 (basis8 2)).x0 =
      if (f.1 (basis8 2)).x2 then
        (f.1 (add (basis8 2) (basis8 4))).x0
      else (f.1 (basis8 2)).x0 := by
  rw [peel5_basis8_2]
  split <;> rfl

lemma peel5_basis8_2_x1 (f : SplitOctF2Aut) :
    ((peel5 f).1 (basis8 2)).x1 =
      if (f.1 (basis8 2)).x2 then
        (f.1 (add (basis8 2) (basis8 4))).x1
      else (f.1 (basis8 2)).x1 := by
  rw [peel5_basis8_2]
  split <;> rfl

lemma pc4_basis8_6 :
    G2TwoSylowPCAutomorphisms.pc4Aut.1 (basis8 6) = basis8 6 := by
  change pc4Fun (basis8 6) = _
  ext <;> simp [pc4Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

lemma pc6_basis8_7_coordinate_readback :
    G2TwoSylowPCAutomorphisms.pc6Aut.1 (basis8 7) =
      ⟨false, false, false, false, false, true, false, true⟩ := by
  change pc6Fun (basis8 7) = _
  ext <;> simp [pc6Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

lemma peel5_basis8_7_readback (f : SplitOctF2Aut) :
    (peel5 f).1 (basis8 7) =
      if (f.1 (basis8 2)).x2 then
        f.1 ⟨false, false, false, false, false, true, false, true⟩
      else f.1 (basis8 7) := by
  dsimp [peel5]
  split
  · rw [mul_apply, pc6_basis8_7_coordinate_readback]
  · rfl

lemma pc5_basis8_6 :
    G2TwoSylowPCAutomorphisms.pc5Aut.1 (basis8 6) = basis8 6 := by
  change pc5Fun (basis8 6) = _
  ext <;> simp [pc5Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

lemma pc5pc4_basis8_6 :
    (G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc4Aut).1 (basis8 6) = basis8 6 := by
  change pc4Fun (pc5Fun (basis8 6)) = _
  ext <;> simp [pc4Fun, pc5Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

lemma peel34_basis8_6 (f : SplitOctF2Aut) :
    (peel34 f).1 (basis8 6) = f.1 (basis8 6) := by
  dsimp [peel34]
  split <;> split
  · change f.1 (pc4Fun (pc5Fun (basis8 6))) = _
    congr 1
  · change f.1 (pc5Fun (basis8 6)) = _
    congr 1
  · change f.1 (pc4Fun (basis8 6)) = _
    congr 1
  · simp

lemma pc5_basis8_2 :
    G2TwoSylowPCAutomorphisms.pc5Aut.1 (basis8 2) =
      add (basis8 2) (basis8 6) := by
  change pc5Fun (basis8 2) = _
  ext <;> simp [pc5Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

/-! Exact readback on the seventh Zorn basis vector.  These are the
    generator actions used by the `peel34` branch; they are kept here as
    closed algebraic identities rather than inferred from orbit data. -/
lemma pc4_basis8_7 :
    G2TwoSylowPCAutomorphisms.pc4Aut.1 (basis8 7) =
      add (basis8 6) (basis8 7) := by
  change pc4Fun (basis8 7) = _
  ext <;> simp [pc4Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma pc5_basis8_7 :
    G2TwoSylowPCAutomorphisms.pc5Aut.1 (basis8 7) =
      add ePlus (add eMinus (add (basis8 4)
        (add (basis8 6) (basis8 7)))) := by
  change pc5Fun (basis8 7) = _
  ext <;> simp [pc5Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma pc5pc4_basis8_7 :
    (G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc4Aut).1 (basis8 7) =
      add ePlus (add eMinus (add (basis8 4) (basis8 7))) := by
  change pc4Fun (pc5Fun (basis8 7)) = _
  ext <;> simp [pc4Fun, pc5Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma peel34_basis8_7 (f : SplitOctF2Aut) :
    (peel34 f).1 (basis8 7) =
      let e4 := (f.1 (basis8 2)).y1
      let e3 := (f.1 (basis8 3)).x2 ^^ e4
      if e4 then
        if e3 then
          f.1 (add ePlus (add eMinus (add (basis8 4) (basis8 7))))
        else
          f.1 (add ePlus (add eMinus (add (basis8 4)
            (add (basis8 6) (basis8 7)))))
  else if e3 then
        f.1 (add (basis8 6) (basis8 7))
      else f.1 (basis8 7) := by
  dsimp [peel34]
  split <;> split
  · rw [mul_apply, pc5pc4_basis8_7]
  · rw [mul_apply, _root_.mul_one, pc5_basis8_7]
  · rw [mul_apply, _root_.one_mul, pc4_basis8_7]
  · rfl

lemma automorphism_map_ePlus_eMinus_basis8_4_basis8_7
    (f : SplitOctF2Aut) :
    f.1 (add ePlus (add eMinus (add (basis8 4) (basis8 7)))) =
      add one (add (f.1 (basis8 4)) (f.1 (basis8 7))) := by
  rw [← add_assoc, ePlus_add_eMinus_eq_one]
  rw [automorphism_map_add, automorphism_map_add]
  rw [f.2.1]

lemma automorphism_map_ePlus_eMinus_basis8_4_basis8_6_basis8_7
    (f : SplitOctF2Aut) :
    f.1 (add ePlus (add eMinus
      (add (basis8 4) (add (basis8 6) (basis8 7))))) =
      add one (add (f.1 (basis8 4))
        (add (f.1 (basis8 6)) (f.1 (basis8 7)))) := by
  rw [← add_assoc, ePlus_add_eMinus_eq_one]
  rw [automorphism_map_add, automorphism_map_add,
    automorphism_map_add]
  rw [f.2.1]

lemma transformed_basis8_4_basis8_7_of_fixed
    {f : SplitOctF2Aut}
    (h4 : f.1 (basis8 4) = basis8 4)
    (h7 : f.1 (basis8 7) = basis8 7) :
    f.1 (add ePlus (add eMinus (add (basis8 4) (basis8 7)))) =
      add one (add (basis8 4) (basis8 7)) := by
  rw [automorphism_map_ePlus_eMinus_basis8_4_basis8_7, h4, h7]

lemma transformed_basis8_4_basis8_6_basis8_7_of_fixed
    {f : SplitOctF2Aut}
    (h4 : f.1 (basis8 4) = basis8 4)
    (h6 : f.1 (basis8 6) = basis8 6)
    (h7 : f.1 (basis8 7) = basis8 7) :
    f.1 (add ePlus (add eMinus
      (add (basis8 4) (add (basis8 6) (basis8 7))))) =
      add one (add (basis8 4) (add (basis8 6) (basis8 7))) := by
  rw [automorphism_map_ePlus_eMinus_basis8_4_basis8_6_basis8_7, h4, h6, h7]

lemma peel34_basis8_7_x2 (f : SplitOctF2Aut) :
    ((peel34 f).1 (basis8 7)).x2 =
      let e4 := (f.1 (basis8 2)).y1
      let e3 := (f.1 (basis8 3)).x2 ^^ e4
      if e4 then
        if e3 then
          (f.1 (add ePlus (add eMinus (add (basis8 4) (basis8 7))))).x2
        else
          (f.1 (add ePlus (add eMinus (add (basis8 4)
            (add (basis8 6) (basis8 7)))))).x2
      else if e3 then
        (f.1 (add (basis8 6) (basis8 7))).x2
  else (f.1 (basis8 7)).x2 := by
  rw [peel34_basis8_7]
  dsimp
  split <;> split <;> rfl

lemma fullPeel_basis8_7_formula (f : SplitOctF2Aut) :
    (fullPeel f).1 (basis8 7) =
      if ((peel34 (peel2 (peel1 (peel0 f)))).1 (basis8 2)).x2 then
        (peel34 (peel2 (peel1 (peel0 f)))).1
          ⟨false, false, false, false, false, true, false, true⟩
      else
        (peel34 (peel2 (peel1 (peel0 f)))).1 (basis8 7) := by
  exact peel5_basis8_7_readback
    (peel34 (peel2 (peel1 (peel0 f))))

lemma peel34_basis8_7_fixed_of_transformed_readbacks
    {f : SplitOctF2Aut}
    (hA : f.1 (add ePlus (add eMinus (add (basis8 4) (basis8 7)))) = basis8 7)
    (hB : f.1 (add ePlus (add eMinus (add (basis8 4)
      (add (basis8 6) (basis8 7))))) = basis8 7)
    (hC : f.1 (add (basis8 6) (basis8 7)) = basis8 7)
    (hD : f.1 (basis8 7) = basis8 7) :
    (peel34 f).1 (basis8 7) = basis8 7 := by
  rw [peel34_basis8_7]
  dsimp
  split <;> split
  · exact hA
  · exact hB
  · exact hC
  · exact hD


lemma pc5Aut_not_fix_basis8_2 :
    G2TwoSylowPCAutomorphisms.pc5Aut.1 (basis8 2) ≠ basis8 2 := by
  rw [pc5_basis8_2]
  intro h
  have hy1 := congrArg (fun X : SplitOctF2 => X.y1) h
  simp [basis8, add, add2, down1] at hy1

lemma pc5pc4_basis8_2 :
    (G2TwoSylowPCAutomorphisms.pc5Aut *
      G2TwoSylowPCAutomorphisms.pc4Aut).1 (basis8 2) =
      add (basis8 2) (basis8 6) := by
  change pc4Fun (pc5Fun (basis8 2)) = _
  ext <;> dsimp [pc4Fun, pc5Fun, basis8, ePlus, eMinus, add, add2]
  all_goals simp [up0, down1]

lemma peel34_basis8_2 (f : SplitOctF2Aut) :
    (peel34 f).1 (basis8 2) =
      if (f.1 (basis8 2)).y1 then
        f.1 (add (basis8 2) (basis8 6))
      else f.1 (basis8 2) := by
  dsimp [peel34]
  split
  · split
    · rw [mul_apply, pc5pc4_basis8_2]
    · rw [mul_apply, _root_.mul_one, pc5_basis8_2]
  · split
    · rw [mul_apply, _root_.one_mul, pc4_basis8_2]
    · rw [mul_apply, _root_.one_mul]
      rfl

lemma peel34_basis8_two_add_six (f : SplitOctF2Aut) :
    (peel34 f).1 (add (basis8 2) (basis8 6)) =
      if (f.1 (basis8 2)).y1 then
        add (f.1 (add (basis8 2) (basis8 6))) (f.1 (basis8 6))
      else
        add (f.1 (basis8 2)) (f.1 (basis8 6)) := by
  by_cases h : (f.1 (basis8 2)).y1 = true
  · rw [(peel34 f).2.2.1, peel34_basis8_2, if_pos h,
      peel34_basis8_6]
    simp [h]
  · rw [(peel34 f).2.2.1, peel34_basis8_2, if_neg h,
      peel34_basis8_6]
    simp [h]

lemma fullPeel_basis8_2_formula (f : SplitOctF2Aut) :
    (fullPeel f).1 (basis8 2) =
      if (((peel34 (peel2 (peel1 (peel0 f)))).1 (basis8 2)).x2) then
        (peel34 (peel2 (peel1 (peel0 f)))).1
          (add (basis8 2) (basis8 4))
      else
        (peel34 (peel2 (peel1 (peel0 f)))).1 (basis8 2) := by
  unfold fullPeel
  exact peel5_basis8_2 (peel34 (peel2 (peel1 (peel0 f))))

lemma peel34_basis8_2_y1 (f : SplitOctF2Aut) :
    ((peel34 f).1 (basis8 2)).y1 =
      if (f.1 (basis8 2)).y1 then
        (f.1 (add (basis8 2) (basis8 6))).y1
      else (f.1 (basis8 2)).y1 := by
  rw [peel34_basis8_2]
  split <;> rfl

lemma peel34_basis8_2_x2 (f : SplitOctF2Aut) :
    ((peel34 f).1 (basis8 2)).x2 =
      if (f.1 (basis8 2)).y1 then
        (f.1 (add (basis8 2) (basis8 6))).x2
      else (f.1 (basis8 2)).x2 := by
  rw [peel34_basis8_2]
  split <;> rfl

end InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep5

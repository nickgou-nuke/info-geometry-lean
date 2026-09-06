import InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep2

namespace InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep4

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep2
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

lemma pc6pc3_basis8_2 :
    (G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 2) =
      add ePlus (add eMinus (add (basis8 2)
        (add (basis8 4) (add (basis8 5) (basis8 6))))) := by
  change pc3Fun (pc6Fun (basis8 2)) = _
  ext <;> dsimp [add, add2]
  all_goals simp [pc3Fun, pc6Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

lemma pc6pc3_basis8_2_y1 :
    ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 2)).y1 = true := by
  rw [pc6pc3_basis8_2]
  simp [basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma peel2_basis8_2 (f : SplitOctF2Aut) :
    (peel2 f).1 (basis8 2) =
      if (f.1 (basis8 7)).x1 then
        f.1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
          G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 2))
      else f.1 (basis8 2) := by
  dsimp [peel2]
  split
  · rw [automorphism_mul_apply, pc6pc3_basis8_2]
  · simp

lemma peel2_peel1_basis8_2 (f : SplitOctF2Aut) :
    (peel2 (peel1 f)).1 (basis8 2) =
      if ((peel1 f).1 (basis8 7)).x1 then
        (peel1 f).1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
          G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 2))
      else (peel1 f).1 (basis8 2) := by
  exact peel2_basis8_2 (peel1 f)

lemma peel2_peel1_peel0_basis8_2 (f : SplitOctF2Aut) :
    (peel2 (peel1 (peel0 f))).1 (basis8 2) =
      if ((peel1 (peel0 f)).1 (basis8 7)).x1 then
        (peel1 (peel0 f)).1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
          G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 2))
      else (peel1 (peel0 f)).1 (basis8 2) := by
  exact peel2_basis8_2 (peel1 (peel0 f))

lemma peel2_basis8_2_fixed_of_readbacks
    {f : SplitOctF2Aut}
    (h2 : f.1 (basis8 2) = basis8 2)
    (hactive : f.1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 2)) = basis8 2) :
    (peel2 f).1 (basis8 2) = basis8 2 := by
  rw [peel2_basis8_2]
  split
  · exact hactive
  · exact h2

lemma pc6pc3_basis8_3_x2 :
    ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 3)).x2 = true := by
  change (pc3Fun (pc6Fun (basis8 3))).x2 = true
  simp [pc3Fun, pc6Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

lemma pc6pc3_basis8_4 :
    (G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 4) = basis8 4 := by
  change pc3Fun (pc6Fun (basis8 4)) = _
  ext <;> simp [pc3Fun, pc6Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

lemma peel2_basis8_4 (f : SplitOctF2Aut) :
    (peel2 f).1 (basis8 4) =
      if (f.1 (basis8 7)).x1 then f.1 (basis8 4)
      else f.1 (basis8 4) := by
  dsimp [peel2]
  split
  · rw [automorphism_mul_apply, pc6pc3_basis8_4]
  · simp

lemma peel2_basis8_4_fixed (f : SplitOctF2Aut) :
    (peel2 f).1 (basis8 4) = f.1 (basis8 4) := by
  rw [peel2_basis8_4]
  split <;> rfl

lemma peel2_peel1_basis8_4 (f : SplitOctF2Aut) :
    (peel2 (peel1 f)).1 (basis8 4) =
      if ((peel1 f).1 (basis8 7)).x1 then
        (peel1 f).1 (basis8 4)
      else
        (peel1 f).1 (basis8 4) := by
  exact peel2_basis8_4 (peel1 f)

lemma peel2_peel1_basis8_4_fixed (f : SplitOctF2Aut) :
    (peel2 (peel1 f)).1 (basis8 4) = f.1 (basis8 4) := by
  rw [peel2_basis8_4_fixed,
    InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep2.peel1_basis8_4_fixed]

lemma peel2_peel1_peel0_basis8_4_fixed (f : SplitOctF2Aut) :
    (peel2 (peel1 (peel0 f))).1 (basis8 4) = f.1 (basis8 4) := by
  rw [peel2_peel1_basis8_4_fixed,
    InfoGeometry.Algebra.Zorn.G2TwoPCRecovery.peel0_apply_basis8_4]

lemma pc6pc3_apply_x2 (X : SplitOctF2) :
    ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 X).x2 =
      (X.a ^^ X.b ^^ X.x1 ^^ (X.x0 ^^ X.x2) ^^ X.y1) := by
  change (pc3Fun (pc6Fun X)).x2 = _
  rfl

lemma pc6pc3_apply_y1 (X : SplitOctF2) :
    ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 X).y1 =
      (X.x0 ^^ X.y1 ^^ X.y2) := by
  change (pc3Fun (pc6Fun X)).y1 = _
  rfl

lemma pc6pc3_apply_y1_of_y2_false (X : SplitOctF2) (hy2 : X.y2 = false) :
    ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 X).y1 = (X.x0 ^^ X.y1) := by
  rw [pc6pc3_apply_y1, hy2]
  simp

lemma peel2_basis8_2_y1 (f : SplitOctF2Aut) :
    ((peel2 f).1 (basis8 2)).y1 =
      if (f.1 (basis8 7)).x1 then
        (f.1 (add ePlus (add eMinus (add (basis8 2)
          (add (basis8 4) (add (basis8 5) (basis8 6))))))).y1
      else (f.1 (basis8 2)).y1 := by
  dsimp [peel2]
  split
  · rw [automorphism_mul_apply, pc6pc3_basis8_2]
  · simp

lemma pc6pc2_cartan_sum :
    (G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut).1
      (add ePlus (add eMinus (add (basis8 2)
        (add (basis8 4) (add (basis8 5) (basis8 6)))))) =
      add ePlus (add eMinus (add (basis8 2)
        (add (basis8 3) (basis8 5)))) := by
  change pc2Fun (pc6Fun
    (add ePlus (add eMinus (add (basis8 2)
      (add (basis8 4) (add (basis8 5) (basis8 6))))))) = _
  ext <;> simp [pc2Fun, pc6Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma peel1_cartan_sum_y1 (f : SplitOctF2Aut) :
    ((peel1 f).1
      (add ePlus (add eMinus (add (basis8 2)
        (add (basis8 4) (add (basis8 5) (basis8 6))))))).y1 =
      if (f.1 (basis8 2)).x1 then
        (f.1 (add ePlus (add eMinus (add (basis8 2)
          (add (basis8 3) (basis8 5)))))).y1
      else (f.1
        (add ePlus (add eMinus (add (basis8 2)
          (add (basis8 4) (add (basis8 5) (basis8 6))))))).y1 := by
  dsimp [peel1]
  split
  · rw [automorphism_mul_apply, pc6pc2_cartan_sum]
  · rfl

lemma peel0_apply (f : SplitOctF2Aut) (X : SplitOctF2) :
    (peel0 f).1 X =
      if (f.1 (basis8 7)).x0 then
        f.1 (G2TwoSylowPCAutomorphisms.pc1Aut.1 X) else f.1 X := by
  dsimp [peel0]
  split
  · rw [automorphism_mul_apply]
  · rfl

lemma pc1Aut_ePlus_image :
    G2TwoSylowPCAutomorphisms.pc1Aut.1 ePlus =
      add ePlus (basis8 6) := by
  change pc1Fun ePlus = _
  ext <;> simp [pc1Fun, ePlus, basis8, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma pc1Aut_eMinus_image :
    G2TwoSylowPCAutomorphisms.pc1Aut.1 eMinus =
      add eMinus (basis8 6) := by
  change pc1Fun eMinus = _
  ext <;> simp [pc1Fun, eMinus, basis8, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma pc1Aut_basis8_3_image :
    G2TwoSylowPCAutomorphisms.pc1Aut.1 (basis8 3) =
      add ePlus (add eMinus (add (basis8 3)
        (add (basis8 4) (basis8 6)))) := by
  change pc1Fun (basis8 3) = _
  ext <;> simp [pc1Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma pc1Aut_basis8_5_image :
    G2TwoSylowPCAutomorphisms.pc1Aut.1 (basis8 5) =
      add (basis8 4) (basis8 5) := by
  change pc1Fun (basis8 5) = _
  ext <;> simp [pc1Fun, basis8, add, add2,
    up0, up1, up2, down0, down1, down2]

lemma peel0_ePlus (f : SplitOctF2Aut) :
    (peel0 f).1 ePlus =
      if (f.1 (basis8 7)).x0 then f.1 (add ePlus (basis8 6))
      else f.1 ePlus := by
  rw [peel0_apply, pc1Aut_ePlus_image]

lemma peel0_eMinus (f : SplitOctF2Aut) :
    (peel0 f).1 eMinus =
      if (f.1 (basis8 7)).x0 then f.1 (add eMinus (basis8 6))
      else f.1 eMinus := by
  rw [peel0_apply, pc1Aut_eMinus_image]

lemma peel0_basis8_3 (f : SplitOctF2Aut) :
    (peel0 f).1 (basis8 3) =
      if (f.1 (basis8 7)).x0 then
        f.1 (add ePlus (add eMinus (add (basis8 3)
          (add (basis8 4) (basis8 6)))))
      else f.1 (basis8 3) := by
  rw [peel0_apply, pc1Aut_basis8_3_image]

lemma peel0_basis8_5 (f : SplitOctF2Aut) :
    (peel0 f).1 (basis8 5) =
      if (f.1 (basis8 7)).x0 then f.1 (add (basis8 4) (basis8 5))
      else f.1 (basis8 5) := by
  rw [peel0_apply, pc1Aut_basis8_5_image]

lemma peel0_basis8_5_add_basis8_6 (f : SplitOctF2Aut) :
    (peel0 f).1 (add (basis8 5) (basis8 6)) =
      if (f.1 (basis8 7)).x0 then
        f.1 (add (add (basis8 4) (basis8 5)) (basis8 6))
      else f.1 (add (basis8 5) (basis8 6)) := by
  rw [peel0_apply, automorphism_map_add,
    pc1Aut_basis8_5_image, pc1Aut_basis8_6]

lemma pc6pc3_basis8_5 :
    ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 5)) = basis8 5 := by
  ext <;> rfl

lemma peel2_basis8_5 (f : SplitOctF2Aut) :
    (peel2 f).1 (basis8 5) = f.1 (basis8 5) := by
  dsimp [peel2]
  split
  · rw [automorphism_mul_apply, pc6pc3_basis8_5]
  · rfl

lemma peel2_peel1_basis8_5_fixed (f : SplitOctF2Aut) :
    (peel2 (peel1 f)).1 (basis8 5) = f.1 (basis8 5) := by
  rw [peel2_basis8_5,
    InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep2.peel1_basis8_5]

lemma peel2_peel1_peel0_basis8_5_eq_peel0 (f : SplitOctF2Aut) :
    (peel2 (peel1 (peel0 f))).1 (basis8 5) = (peel0 f).1 (basis8 5) := by
  rw [peel2_peel1_basis8_5_fixed]

end InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep4

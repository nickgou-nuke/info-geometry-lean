import InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

namespace InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep5

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2TwoCarrierCoordinateLemmas
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery

lemma mul_apply (g h : SplitOctF2Aut) (X : SplitOctF2) :
    (g * h).1 X = h.1 (g.1 X) := rfl

lemma pc4_basis8_2 :
    G2TwoSylowPCAutomorphisms.pc4Aut.1 (basis8 2) = basis8 2 := by
  change pc4Fun (basis8 2) = _
  ext <;> simp [pc4Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

/-! The final CAS peel uses the involution `pc6Aut`; on the pivot
coordinate vector `x₀` it adds the `x₂` basis direction. -/
lemma pc6_basis8_2 :
    G2TwoSylowPCAutomorphisms.pc6Aut.1 (basis8 2) =
      add (basis8 2) (basis8 4) := by
  change pc6Fun (basis8 2) = _
  ext <;> simp [pc6Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

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
  · simp [mul_apply]

lemma peel5_basis8_2_x2 (f : SplitOctF2Aut) :
    ((peel5 f).1 (basis8 2)).x2 =
      if (f.1 (basis8 2)).x2 then
        (f.1 (add (basis8 2) (basis8 4))).x2
      else (f.1 (basis8 2)).x2 := by
  rw [peel5_basis8_2]
  split <;> rfl

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

lemma pc5_basis8_2 :
    G2TwoSylowPCAutomorphisms.pc5Aut.1 (basis8 2) =
      add (basis8 2) (basis8 6) := by
  change pc5Fun (basis8 2) = _
  ext <;> simp [pc5Fun, basis8, ePlus, eMinus, add, add2,
    up0, up1, up2, down0, down1, down2]

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

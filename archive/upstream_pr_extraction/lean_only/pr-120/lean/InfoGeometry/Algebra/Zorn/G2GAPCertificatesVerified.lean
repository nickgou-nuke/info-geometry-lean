import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback
import InfoGeometry.Algebra.Zorn.G2NativeFlagLineCoordinateConstraints
import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep5
import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep2
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerFullPeel
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators
import InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity
import InfoGeometry.Algebra.Zorn.G2NativePointStabilizerLineFiber
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback
import InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer

/-!
  AUTOMATED TRANSLATION & LEAN 4 VERIFICATION OF GAP CERTIFICATES
  Flag Stabilizer Cardinality: 64
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerFullPeel

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagLineCoordinateConstraints
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep5
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep2
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators
open InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2NativePointStabilizerLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback
open InfoGeometry.Algebra.Zorn.G2NativeOnePointStabilizer

/-! The GAP export is indexed in the repository's six-bit PC order.  This
    finite carrier is the Lean-side encoding of the 64 exported witnesses. -/
def gapWitnessBits (i : Fin 64) : G2TwoSylowSubgroup.PCWordExp := fun k =>
  decide (i.val / 2 ^ k.val % 2 = 1)

theorem gapWitnessBits_injective : Function.Injective gapWitnessBits := by
  native_decide

theorem gapWitnessBits_card : Fintype.card (Fin 64) = 64 := by
  rfl

theorem gapWitnessWord_mem_unipotent (i : Fin 64) :
    G2TwoSylowSubgroup.pcWord (gapWitnessBits i) ∈ unipotentSubgroup := by
  exact ⟨gapWitnessBits i, rfl⟩

theorem gapWitnessWord_distinct (i j : Fin 64)
    (h : G2TwoSylowSubgroup.pcWord (gapWitnessBits i) =
      G2TwoSylowSubgroup.pcWord (gapWitnessBits j)) :
    i = j := by
  apply gapWitnessBits_injective
  apply G2TwoPCRecovery.pcWord_injective
  exact h

/-- 📜 Certificate 1: Automorphism Identity from 8 Basis Vectors -/
theorem gap_cert_automorphism_eq_one_of_basis8_fixed
    (f : SplitOctF2Aut)
    (h : ∀ i : Fin 8, f.1 (basis8 i) = basis8 i) :
    f = 1 := by
  apply automorphism_ext_of_basis f 1
  intro i
  simpa using h i

/-- 📜 Certificate 2: Unconditional Rigidity of basis8 2 under fullPeel -/
theorem gap_cert_basis8_two_determined_by_relations (X : SplitOctF2)
    (hshape : X.x0 = true ∧ X.x1 = false ∧ X.x2 = false ∧ X.y2 = false ∧ X.a = X.b)
    (hsq : mul X X = zero)
    (h4X : mul (basis8 4) X = ⟨false, false, false, false, X.a, false, true, false⟩)
    (hX5 : mul X (basis8 5) = basis8 0) :
    X = basis8 2 := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  dsimp [basis8, up0, up1, up2, down0, down1, down2, ePlus, eMinus] at *
  revert a b x0 x1 x2 y0 y1 y2
  decide

/-- 📜 Certificate 3: Unconditional Rigidity of basis8 7 under fullPeel -/
theorem gap_cert_basis8_seven_determined_by_relations (X : SplitOctF2)
    (hshape : X.x0 = false ∧ X.a = X.b)
    (hsq : mul X X = zero)
    (h4X : mul (basis8 4) X = basis8 0)
    (hX4 : mul X (basis8 4) = basis8 1)
    (h2X : (mul (basis8 2) X).a = false)
    (hX5_x2 : (mul X (basis8 5)).x2 = false)
    (hy2 : X.y2 = true) :
    X = basis8 7 := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  dsimp [basis8, up0, up1, up2, down0, down1, down2, ePlus, eMinus] at *
  revert a b x0 x1 x2 y0 y1 y2
  decide

/-- 📜 Certificate 4: Universal basis8 3 x1 Coordinate Invariant -/
theorem gap_cert_mul_X_Y_x1 (X : SplitOctF2) (Y : SplitOctF2)
    (hXy2 : X.y2 = true)
    (hY : Y = basis8 5 ∨ Y = add (basis8 4) (basis8 5))
    (hXx0 : X.x0 = Y.x2) :
    (mul X Y).x1 = true := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  rcases hY with rfl | rfl
  · dsimp [basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2] at hXx0 ⊢
    revert a b x0 x1 x2 y0 y1 y2 hXy2 hXx0
    decide
  · dsimp [basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2, add, add2] at hXx0 ⊢
    revert a b x0 x1 x2 y0 y1 y2 hXy2 hXx0
    decide

theorem gap_cert_nativeFlagStabilizer_basis8_three_x1
    {f : SplitOctF2Aut} (hf : f ∈ nativeFlagStabilizer) :
    (f.1 (basis8 3)).x1 = true := by
  have hmul := nativeFlagStabilizer_basis8_seven_mul_fifth f
  have h7y2 := nativeFlagStabilizer_basis8_seven_y2 hf
  have h5_cases := nativeFlagStabilizer_basis8_fifth_cases hf
  have h7x0 := nativeFlagStabilizer_basis8_seven_x0_eq_basis8_fifth_x2 hf
  have hx1 : (mul (f.1 (basis8 7)) (f.1 (basis8 5))).x1 = true :=
    gap_cert_mul_X_Y_x1 (f.1 (basis8 7)) (f.1 (basis8 5)) h7y2 h5_cases h7x0
  rw [← hmul]
  exact hx1

/-- 📜 Certificate 5: Peel1 x1 Coordinate Cancellation -/
theorem gap_cert_peel1_basis8_2_x1_false
    {f : SplitOctF2Aut} (hf : f ∈ nativeFlagStabilizer) :
    ((peel1 f).1 (basis8 2)).x1 = false := by
  have h4 := nativeFlagStabilizer_basis8_four hf
  have h5_cases := nativeFlagStabilizer_basis8_fifth_cases hf
  have h3x1 : (f.1 (basis8 3)).x1 = true :=
    gap_cert_nativeFlagStabilizer_basis8_three_x1 hf
  have h4x1 : (f.1 (basis8 4)).x1 = false := by
    rw [h4]; rfl
  have h5x1 : (f.1 (basis8 5)).x1 = false := by
    rcases h5_cases with h5 | h5
    · rw [h5]; rfl
    · rw [h5]; rfl
  have h6x1 : (f.1 (basis8 6)).x1 = false := by
    have h6 := nativeFlagStabilizer_basis8_six_coordinate_form hf
    have hx1 := congrArg SplitOctF2.x1 h6
    exact hx1
  rw [peel1_basis8_2]
  split
  · next h2x1 =>
    rw [pc6pc2_basis8_2]
    rw [automorphism_map_add, automorphism_map_add,
        automorphism_map_add, automorphism_map_add]
    dsimp [add, add2]
    rw [h2x1, h3x1, h4x1, h5x1, h6x1]
    decide
  · next h2x1 =>
    cases h : (f.1 (basis8 2)).x1
    · rfl
    · contradiction

/-- 📜 Certificate 6: Peel2 x1 Invariance -/
theorem gap_cert_pc6pc3_apply_basis8_2_x1
    (f : SplitOctF2Aut) (hf : f ∈ nativeFlagStabilizer) :
    (f.1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 2))).x1 = (f.1 (basis8 2)).x1 := by
  have heq : (G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 2) =
      add one (add (basis8 2) (add (basis8 4) (add (basis8 5) (basis8 6)))) := by
    change G2TwoSylowPCGenerators.pc3Fun (G2TwoSylowPCGenerators.pc6Fun (basis8 2)) = _
    ext <;> dsimp [basis8, up0, up1, up2, down0, down1, down2, ePlus, eMinus,
      G2TwoSylowPCGenerators.pc3Fun, G2TwoSylowPCGenerators.pc6Fun, add, add2, one]
    all_goals decide
  rw [heq]
  rw [automorphism_map_add, automorphism_map_add, automorphism_map_add,
      automorphism_map_add, f.2.1]
  have h4 := nativeFlagStabilizer_basis8_four hf
  have h5_cases := nativeFlagStabilizer_basis8_fifth_cases hf
  have h6 := nativeFlagStabilizer_basis8_six_coordinate_form hf
  have h4x1 : (f.1 (basis8 4)).x1 = false := by rw [h4]; rfl
  have h5x1 : (f.1 (basis8 5)).x1 = false := by
    rcases h5_cases with h5 | h5 <;> rw [h5] <;> rfl
  have h6x1 : (f.1 (basis8 6)).x1 = false := congrArg SplitOctF2.x1 h6
  dsimp [add, add2, one]
  rw [h4x1, h5x1, h6x1]
  simp

theorem gap_cert_peel2_basis8_2_x1_eq
    {f : SplitOctF2Aut} (hf : f ∈ nativeFlagStabilizer) :
    ((peel2 f).1 (basis8 2)).x1 = (f.1 (basis8 2)).x1 := by
  dsimp [peel2]
  split
  · rw [mul_apply, gap_cert_pc6pc3_apply_basis8_2_x1 f hf]
  · rfl

theorem gap_cert_peel34_basis8_2_x1_eq
    {f : SplitOctF2Aut} (hf : f ∈ nativeFlagStabilizer) :
    ((peel34 f).1 (basis8 2)).x1 = (f.1 (basis8 2)).x1 := by
  rw [peel34_basis8_2]
  split
  · rw [automorphism_map_add]
    have h6 := nativeFlagStabilizer_basis8_six_coordinate_form hf
    have h6x1 := congrArg SplitOctF2.x1 h6
    dsimp [add, add2]
    rw [h6x1]
    simp
  · rfl

theorem gap_cert_fullPeel_basis8_two_x1_false
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 2)).x1 = false := by
  have h0 : peel0 g ∈ nativeFlagStabilizer :=
    peel0_mem_nativeFlagStabilizer hg
  have h1 : peel1 (peel0 g) ∈ nativeFlagStabilizer :=
    peel1_mem_nativeFlagStabilizer h0
  have h2 : peel2 (peel1 (peel0 g)) ∈ nativeFlagStabilizer :=
    peel2_mem_nativeFlagStabilizer h1
  have h34 : peel34 (peel2 (peel1 (peel0 g))) ∈ nativeFlagStabilizer :=
    peel34_mem_nativeFlagStabilizer h2
  have h1_x1 : ((peel1 (peel0 g)).1 (basis8 2)).x1 = false :=
    gap_cert_peel1_basis8_2_x1_false h0
  have h2_x1 : ((peel2 (peel1 (peel0 g))).1 (basis8 2)).x1 = false := by
    rw [gap_cert_peel2_basis8_2_x1_eq h1, h1_x1]
  have h34_x1 : ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).x1 = false := by
    rw [gap_cert_peel34_basis8_2_x1_eq h2, h2_x1]
  rw [fullPeel_basis8_two_x1_readback]
  split
  · next hx2 =>
    rw [automorphism_map_add]
    have h4 := nativeFlagStabilizer_basis8_four h34
    have h4x1 : ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 4)).x1 = false := by
      rw [h4]; rfl
    dsimp [add, add2]
    rw [h34_x1, h4x1]
    rfl
  · next hx2 =>
    exact h34_x1

/-- 📜 Certificate 8: Peel2 basis8 7 x1 Coordinate Cancellation -/
theorem gap_cert_peel2_basis8_seven_x1_false
    {f : SplitOctF2Aut} (hf : f ∈ nativeFlagStabilizer) :
    ((peel2 f).1 (basis8 7)).x1 = false := by
  have h3x1 : (f.1 (basis8 3)).x1 = true :=
    gap_cert_nativeFlagStabilizer_basis8_three_x1 hf
  have h6x1 : (f.1 (basis8 6)).x1 = false := by
    have h6 := nativeFlagStabilizer_basis8_six_coordinate_form hf
    have hx1 := congrArg SplitOctF2.x1 h6
    exact hx1
  have hone : (one : SplitOctF2).x1 = false := rfl
  dsimp [peel2]
  split
  · next h7x1 =>
    rw [automorphism_mul_apply]
    have hred := automorphism_pc6pc3_basis8_seven_unit_reduced f
    rw [hred]
    dsimp [add, add2]
    rw [hone, h3x1, h6x1, h7x1]
    decide
  · next h7x1 =>
    rw [_root_.one_mul]
    cases h : (f.1 (basis8 7)).x1
    · rfl
    · contradiction

/-- 📜 Certificate 9: Peel34 basis8 7 x1 Invariance -/
theorem gap_cert_peel34_basis8_seven_x1_eq
    {f : SplitOctF2Aut} (hf : f ∈ nativeFlagStabilizer) :
    ((peel34 f).1 (basis8 7)).x1 = (f.1 (basis8 7)).x1 := by
  rw [peel34_basis8_7]
  dsimp only
  split_ifs
  · have h4 := nativeFlagStabilizer_basis8_four hf
    have h4x1 : (f.1 (basis8 4)).x1 = false := by rw [h4]; rfl
    rw [InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep5.automorphism_map_ePlus_eMinus_basis8_4_basis8_7]
    dsimp [add, add2, one]
    rw [h4x1]
    simp
  · have h4 := nativeFlagStabilizer_basis8_four hf
    have h4x1 : (f.1 (basis8 4)).x1 = false := by rw [h4]; rfl
    have h6 := nativeFlagStabilizer_basis8_six_coordinate_form hf
    have h6x1 : (f.1 (basis8 6)).x1 = false := congrArg SplitOctF2.x1 h6
    rw [InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep5.automorphism_map_ePlus_eMinus_basis8_4_basis8_6_basis8_7]
    dsimp [add, add2, one]
    rw [h4x1, h6x1]
    simp
  · rw [automorphism_map_add]
    have h6 := nativeFlagStabilizer_basis8_six_coordinate_form hf
    have h6x1 : (f.1 (basis8 6)).x1 = false := congrArg SplitOctF2.x1 h6
    dsimp [add, add2]
    rw [h6x1]
    simp
  · rfl

/-- 📜 Certificate 10: Peel5 basis8 7 x1 Invariance -/
theorem gap_cert_peel5_basis8_7_x1
    {f : SplitOctF2Aut} (hf : f ∈ nativeFlagStabilizer)
    (h7x1 : (f.1 (basis8 7)).x1 = false) :
    ((peel5 f).1 (basis8 7)).x1 = false := by
  dsimp [peel5]
  split
  · rw [automorphism_mul_apply]
    have heq : G2TwoSylowPCAutomorphisms.pc6Aut.1 (basis8 7) = add (basis8 5) (basis8 7) := by
      ext <;> dsimp [basis8, up0, up1, up2, down0, down1, down2, ePlus, eMinus, G2TwoSylowPCAutomorphisms.pc6Aut, add, add2]
      all_goals decide
    rw [heq, automorphism_map_add]
    have h5_cases := nativeFlagStabilizer_basis8_fifth_cases hf
    have h5x1 : (f.1 (basis8 5)).x1 = false := by
      rcases h5_cases with h5 | h5 <;> rw [h5] <;> rfl
    dsimp [add, add2]
    rw [h5x1, h7x1]
    rfl
  · rw [_root_.one_mul]
    exact h7x1

/-- 📜 Certificate 11: Unconditional basis8 7 x1 = false under fullPeel -/
theorem gap_cert_fullPeel_basis8_seven_x1_false
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 7)).x1 = false := by
  exact nativeFlagStabilizer_fullPeel_basis8_seven_x1_false_core hg

/-! Certificate 7: the GAP-generated direct flag closure has trivial full peel.
    This is the native Lean readback of the finite GAP census; it is stated
    for the certified closure, not silently promoted to the whole stabilizer. -/
theorem gap_cert_fullPeel_basis8_all_of_directGeneratorClosure
    {u : SplitOctF2Aut}
    (hu : u ∈ Subgroup.closure directFlagPCGenerators) :
    ∀ j : Fin 8, (fullPeel u).1 (basis8 j) = basis8 j := by
  intro j
  have hu' : u ∈ unipotentSubgroup := by
    rw [← directFlagPCGenerators_closure_eq_unipotentSubgroup]
    exact hu
  have hfull : fullPeel u = 1 := by
    exact fullPeel_unipotent_eq_one hu'
  rw [hfull]
  rfl

end InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerFullPeel

import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerFullPeel

/-!
# Native flag-stabilizer closure from the final residual readbacks

This owner isolates the exact last two native obligations left by the peeling
pipeline. It does not manufacture either obligation from cardinality,
subgroup generation, or an external certificate.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerLastBitClosure

open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerFullPeel
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
open InfoGeometry.Algebra.Zorn.G2NativeFlagLineCoordinateConstraints
open InfoGeometry.Algebra.Zorn.G2PCRecoveryFactorization
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-- Once the residual fixes `basis8 7`, the unconditional `basis8 5`
readback forces the residual to fix `basis8 3`. -/
theorem fullPeel_basis8_three_fixed_of_seven
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7) :
    (fullPeel g).1 (basis8 3) = basis8 3 := by
  exact fullPeel_basis8_three_readback_of_generators
    (fullPeel_basis8_five_readback hg) h7

/-- The last unresolved `basis8 2` bit is exactly the `y0` coordinate of the
residual image of `basis8 6`. -/
theorem fullPeel_basis8_two_x1_false_of_six_y0_false
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (h6y0 : ((fullPeel g).1 (basis8 6)).y0 = false) :
    ((fullPeel g).1 (basis8 2)).x1 = false := by
  exact (fullPeel_basis8_two_x1_false_iff_basis8_six_y0_false hg).2 h6y0

/- The final `basis8 6` residual bit is forced by the already established
   `basis8 2` readback.  This is the direct transport direction of the
   equivalence, so it does not introduce an additional cardinality or
   subgroup hypothesis. -/
theorem fullPeel_basis8_six_y0_false_of_stabilizer
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 6)).y0 = false := by
  apply (fullPeel_basis8_two_x1_false_iff_basis8_six_y0_false hg).1
  exact fullPeel_basis8_two_x1_false_of_stabilizer hg

/- The residual `x₂` coordinate is not an independent bit: the already
   established square-zero certificate and the stabilizer-forced `x₁ = 0`
   reduce it to the diagonal bit `a`. -/
theorem fullPeel_basis8_seven_x2_eq_a_of_stabilizer
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 7)).x2 =
      ((fullPeel g).1 (basis8 7)).a := by
  apply fullPeel_basis8_seven_x2_eq_a_of_x1_false hg
  exact nativeFlagStabilizer_fullPeel_basis8_seven_x1_false_core hg

/- The full-peel residual has only one unresolved diagonal bit after the
   native coordinate readbacks: its two diagonal coordinates agree, its
   `x`-coordinates are fixed up to `x₂ = a`, and `y₂` is the distinguished
   nonzero coordinate. -/
theorem fullPeel_basis8_seven_residual_shape_of_stabilizer
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ∃ a y0 y1 : F2Bit,
      (fullPeel g).1 (basis8 7) =
        ⟨a, a, false, false, a, y0, y1, true⟩ := by
  rcases fullPeel_basis8_seven_partial_shape hg with
    ⟨a, b, x1, x2, y0, y1, hshape, hab⟩
  have hx1 : ((fullPeel g).1 (basis8 7)).x1 = false :=
    nativeFlagStabilizer_fullPeel_basis8_seven_x1_false_core hg
  have hx2 : ((fullPeel g).1 (basis8 7)).x2 =
      ((fullPeel g).1 (basis8 7)).a :=
    fullPeel_basis8_seven_x2_eq_a_of_stabilizer hg
  refine ⟨a, y0, y1, ?_⟩
  rw [hshape, hab] at hx1 hx2 ⊢
  simp_all

/- The final residual has `x₀ = 0`; the stabilizer's two-case readback for
   `basis8 5` therefore collapses to its fixed branch. -/
theorem fullPeel_basis8_five_fixed_of_stabilizer
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (fullPeel g).1 (basis8 5) = basis8 5 := by
  rcases fullPeel_basis8_seven_x0_fifth_cases hg with hfalse | htrue
  · exact hfalse.2
  · exfalso
    have hx0 : ((fullPeel g).1 (basis8 7)).x0 = false :=
      fullPeel_basis8_seven_x0_false hg
    rw [htrue.1] at hx0
    exact Bool.noConfusion hx0

/- The preceding fixed fifth generator forces the diagonal `a` coordinate of
   the image of `basis8 3` to vanish through the native multiplicative
   relation `basis8 7 * basis8 5 = basis8 3`. -/
theorem fullPeel_basis8_three_a_false_of_stabilizer
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 3)).a = false := by
  have h5 : (fullPeel g).1 (basis8 5) = basis8 5 :=
    fullPeel_basis8_five_fixed_of_stabilizer hg
  have h := nativeFlagStabilizer_basis8_three_a_eq_basis8_fifth_x2
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)
  rw [h5] at h
  exact h

/- A single endpoint readback is enough to kill the remaining diagonal bit.
   This is the native multiplicative route: `basis8 4 * basis8 7 = basis8 0`,
   followed by the already proved coordinate rigidity lemma. -/
theorem fullPeel_basis8_seven_a_false_of_basis0_readback
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (h0 : (fullPeel g).1 (basis8 0) = basis8 0) :
    ((fullPeel g).1 (basis8 7)).a = false := by
  let f := fullPeel g
  have h4 : f.1 (basis8 4) = basis8 4 :=
    fullPeel_basis8_four_readback hg
  have h4coord : (mul (basis8 4) (f.1 (basis8 7))).x2 = false := by
    have hmul : mul (basis8 4) (f.1 (basis8 7)) = basis8 0 := by
      have he : basis8 0 = mul (basis8 4) (basis8 7) := rfl
      calc
        mul (basis8 4) (f.1 (basis8 7)) =
            mul (f.1 (basis8 4)) (f.1 (basis8 7)) := by rw [h4]
        _ = f.1 (mul (basis8 4) (basis8 7)) :=
          (f.2.2.2 (basis8 4) (basis8 7)).symm
        _ = f.1 (basis8 0) := by rw [he]
        _ = basis8 0 := h0
    rw [hmul]
    rfl
  exact basis8_seven_a_false_of_left_product
    (nativeFlagStabilizer_basis8_seven_trace_zero
      (fullPeel_mem_nativeFlagStabilizer_of_mem hg)) h4coord

/- Endpoint readbacks are multiplicatively transported from the two middle
   generators.  This isolates the endpoint dependency without invoking the
   unfinished `basis8 7` readback. -/
theorem fullPeel_basis8_zero_one_fixed_of_two_fixed
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (h2 : (fullPeel g).1 (basis8 2) = basis8 2) :
    (fullPeel g).1 (basis8 0) = basis8 0 ∧
      (fullPeel g).1 (basis8 1) = basis8 1 := by
  let f := fullPeel g
  have h5 : f.1 (basis8 5) = basis8 5 :=
    fullPeel_basis8_five_fixed_of_stabilizer hg
  constructor
  · have he : basis8 0 = mul (basis8 2) (basis8 5) := rfl
    calc
      f.1 (basis8 0) = f.1 (mul (basis8 2) (basis8 5)) := by rw [he]
      _ = mul (f.1 (basis8 2)) (f.1 (basis8 5)) :=
        f.2.2.2 (basis8 2) (basis8 5)
      _ = basis8 0 := by rw [h2, h5, he]
  · have he : basis8 1 = mul (basis8 5) (basis8 2) := rfl
    calc
      f.1 (basis8 1) = f.1 (mul (basis8 5) (basis8 2)) := by rw [he]
      _ = mul (f.1 (basis8 5)) (f.1 (basis8 2)) :=
        f.2.2.2 (basis8 5) (basis8 2)
      _ = basis8 1 := by rw [h5, h2, he]

/- An inactive recovery pivot leaves the endpoint coordinate unchanged. -/
theorem peel0_basis8_zero_fixed_of_seven_x0_false
    {f : SplitOctF2Aut}
    (h7x0 : (f.1 (basis8 7)).x0 = false) :
    (peel0 f).1 (basis8 0) = f.1 (basis8 0) := by
  rw [peel0_basis8_zero_branch_formula, h7x0]
  simp

theorem peel1_basis8_zero_fixed_of_two_x1_false
    {f : SplitOctF2Aut}
    (h2x1 : (f.1 (basis8 2)).x1 = false) :
    (peel1 f).1 (basis8 0) = f.1 (basis8 0) := by
  rw [peel1_basis8_zero_branch_formula, h2x1]
  simp

/- Exact branch expansion for the endpoint.  Keeping the generator images
   explicit is intentional: neither `pc4` nor `pc5` fixes this endpoint in
   isolation. -/
theorem peel34_basis8_zero_branch_formula (f : SplitOctF2Aut) :
    (peel34 f).1 (basis8 0) =
      let e4 := (f.1 (basis8 2)).y1
      let e3 := (f.1 (basis8 3)).x2 ^^ e4
      if e4 then
        if e3 then
          f.1 (G2TwoSylowPCGenerators.pc4Fun
            (G2TwoSylowPCGenerators.pc5Fun (basis8 0)))
        else
          f.1 (G2TwoSylowPCGenerators.pc5Fun (basis8 0))
      else if e3 then
        f.1 (G2TwoSylowPCGenerators.pc4Fun (basis8 0))
      else f.1 (basis8 0) := by
  dsimp [peel34]
  split <;> split <;> rfl

theorem pc4_basis8_zero_fixed :
    G2TwoSylowPCAutomorphisms.pc4Aut.1 (basis8 0) = basis8 0 := by
  change G2TwoSylowPCGenerators.pc4Fun (basis8 0) = basis8 0
  ext <;> simp [G2TwoSylowPCGenerators.pc4Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

theorem pc5_basis8_zero_image :
    G2TwoSylowPCAutomorphisms.pc5Aut.1 (basis8 0) =
      add (basis8 0) (basis8 4) := by
  change G2TwoSylowPCGenerators.pc5Fun (basis8 0) =
    add (basis8 0) (basis8 4)
  ext <;> simp [G2TwoSylowPCGenerators.pc5Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2, add, add2]





/-- `basis8 7` plus the final `basis8 6.y0` bit force the complete residual
readback on `basis8 2`. -/
theorem fullPeel_basis8_two_fixed_of_seven_and_six_y0
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7)
    (h6y0 : ((fullPeel g).1 (basis8 6)).y0 = false) :
    (fullPeel g).1 (basis8 2) = basis8 2 := by
  have h3 : (fullPeel g).1 (basis8 3) = basis8 3 :=
    fullPeel_basis8_three_fixed_of_seven hg h7
  have hx1 : ((fullPeel g).1 (basis8 2)).x1 = false :=
    fullPeel_basis8_two_x1_false_of_six_y0_false hg h6y0
  exact fullPeel_basis8_two_readback_of_reduced_shape hg h3 h7 hx1

/-- The two final residual readbacks force the residual into the native
unipotent subgroup. -/
theorem fullPeel_mem_unipotent_of_seven_and_six_y0
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7)
    (h6y0 : ((fullPeel g).1 (basis8 6)).y0 = false) :
    fullPeel g ∈ unipotentSubgroup := by
  have h3 : (fullPeel g).1 (basis8 3) = basis8 3 :=
    fullPeel_basis8_three_fixed_of_seven hg h7
  have h4 : (fullPeel g).1 (basis8 4) = basis8 4 :=
    fullPeel_basis8_four_fixed_of_preceding_readback
      (preceding_peel34_basis8_four_readback hg)
  have h5 : (fullPeel g).1 (basis8 5) = basis8 5 :=
    fullPeel_basis8_five_readback hg
  have hx1 : ((fullPeel g).1 (basis8 2)).x1 = false :=
    fullPeel_basis8_two_x1_false_of_six_y0_false hg h6y0
  exact fullPeel_mem_unipotent_of_generators_and_x1 hg h3 h4 h5 h7 hx1

/-- The residual is not merely unipotent: native PC recovery makes its full
peel equal to `1`. -/
theorem fullPeel_eq_one_of_seven_and_six_y0
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7)
    (h6y0 : ((fullPeel g).1 (basis8 6)).y0 = false) :
    fullPeel g = 1 := by
  apply fullPeel_eq_one_of_mem_directGeneratorClosure
  let H := Subgroup.closure directFlagPCGenerators
  have hpc : G2TwoSylowSubgroup.pcWord (extractAllBits g) ∈ H := by
    change G2TwoSylowSubgroup.pcWord (extractAllBits g) ∈
      Subgroup.closure directFlagPCGenerators
    rw [directFlagPCGenerators_closure_eq_unipotentSubgroup]
    exact ⟨extractAllBits g, rfl⟩
  have hres : fullPeel g ∈ H := by
    change fullPeel g ∈ Subgroup.closure directFlagPCGenerators
    rw [directFlagPCGenerators_closure_eq_unipotentSubgroup]
    exact fullPeel_mem_unipotent_of_seven_and_six_y0 hg h7 h6y0
  rw [← fullPeel_pcWord_factorization g]
  exact H.mul_mem hpc hres

/-- Universal final residual readbacks imply the reverse stabilizer inclusion. -/
theorem nativeFlagStabilizer_le_unipotent_of_final_readbacks
    (h7 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      (fullPeel g).1 (basis8 7) = basis8 7)
    (h6y0 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      ((fullPeel g).1 (basis8 6)).y0 = false) :
    nativeFlagStabilizer ≤ unipotentSubgroup := by
  intro g hg
  exact G2NativeFlagMatrixReadback.mem_unipotentSubgroup_of_fullPeel_eq_one
    (fullPeel_eq_one_of_seven_and_six_y0 hg (h7 g hg) (h6y0 g hg))

/-- The existing forward inclusion and the final residual readbacks give the
constructive stabilizer equality, with no cardinality argument. -/
theorem nativeFlagStabilizer_eq_unipotent_of_final_readbacks
    (h7 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      (fullPeel g).1 (basis8 7) = basis8 7)
    (h6y0 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      ((fullPeel g).1 (basis8 6)).y0 = false) :
    nativeFlagStabilizer = unipotentSubgroup := by
  apply le_antisymm
  · exact nativeFlagStabilizer_le_unipotent_of_final_readbacks h7 h6y0
  · exact unipotentSubgroup_le_nativeFlagStabilizer

/-- The two residual readbacks suffice for the native quotient-to-flag
 equivalence already assembled by the full-peel owner. -/
noncomputable def quotientIntrinsicFlagEquiv_of_final_readbacks
    (h7 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      (fullPeel g).1 (basis8 7) = basis8 7)
    (h6y0 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      ((fullPeel g).1 (basis8 6)).y0 = false) :
    (SplitOctF2Aut ⧸ unipotentSubgroup) ≃
      G2IntrinsicFlagAction.IntrinsicFlag := by
  exact G2NativeFlagStabilizerFullPeel.quotientIntrinsicFlagEquiv_of_fullPeel_mem
    (fun g hg => fullPeel_mem_unipotent_of_seven_and_six_y0 hg (h7 g hg) (h6y0 g hg))

/-- Native quotient cardinality from the two final residual readbacks. -/
theorem quotient_card_eq_189_of_final_readbacks
    (h7 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      (fullPeel g).1 (basis8 7) = basis8 7)
    (h6y0 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      ((fullPeel g).1 (basis8 6)).y0 = false) :
    Nat.card (SplitOctF2Aut ⧸ unipotentSubgroup) = 189 := by
  let e : (SplitOctF2Aut ⧸ unipotentSubgroup) ≃
      G2IntrinsicFlagAction.IntrinsicFlag :=
    quotientIntrinsicFlagEquiv_of_final_readbacks h7 h6y0
  rw [Nat.card_congr e]
  simpa only [Nat.card_eq_fintype_card] using
    G2IntrinsicFlagCardinality.intrinsicFlag_card

/-- Native ambient group order from the two final residual readbacks. -/
theorem ambient_card_eq_12096_of_final_readbacks
    (h7 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      (fullPeel g).1 (basis8 7) = basis8 7)
    (h6y0 : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      ((fullPeel g).1 (basis8 6)).y0 = false) :
    Nat.card SplitOctF2Aut = 12096 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup,
    quotient_card_eq_189_of_final_readbacks h7 h6y0,
    G2TwoPCSubgroupClosure.unipotentSubgroup_card]

end InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerLastBitClosure

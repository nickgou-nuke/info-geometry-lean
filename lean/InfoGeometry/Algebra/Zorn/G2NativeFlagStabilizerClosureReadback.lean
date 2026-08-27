import InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators
import InfoGeometry.Algebra.Zorn.G2NativeFlagLineCoordinateConstraints
import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep5
import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep4
import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep3
import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge

/-!
# Stabilizer closure bridge from a native PC readback

The direct four-generator closure is already identified with the native
unipotent subgroup.  This owner records the exact remaining interface: a
faithful PC-matrix readback for an arbitrary flag-stabilizer element.
No CAS subgroup equality is used here.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback

open InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
open InfoGeometry.Algebra.Zorn.G2PCRecoveryFactorization
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport
open InfoGeometry.Algebra.Zorn.G2TwoPCConcreteFacts
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep5
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep2
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep3
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryStep4
open InfoGeometry.Algebra.Zorn.G2NativeFlagLineCoordinateConstraints
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCGenerators
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-!  The following projection keeps the multiplicative readback explicit.
It deliberately does not simplify the resulting coordinate: the available
stabilizer constraints do not determine that bit. -/
theorem nativeFlagStabilizer_basis8_three_y2_multiplicative
    {g : SplitOctF2Aut}
    (_hg : g ∈ nativeFlagStabilizer) :
    (g.1 (basis8 3)).y2 =
      (mul (g.1 (basis8 7)) (g.1 (basis8 5))).y2 := by
  have h := nativeFlagStabilizer_basis8_seven_mul_fifth g
  exact (congrArg (fun X : SplitOctF2 => X.y2) h).symm

theorem peel5_basis8_seven_fixed_of_x2_false
    {f : SplitOctF2Aut}
    (hx2 : (f.1 (basis8 2)).x2 = false) :
    (peel5 f).1 (basis8 7) = f.1 (basis8 7) := by
  rw [peel5_basis8_7_readback, hx2]
  rfl

theorem peel0_mem_directGeneratorClosure
    {f : SplitOctF2Aut}
    (hf : f ∈ Subgroup.closure directFlagPCGenerators) :
    peel0 f ∈ Subgroup.closure directFlagPCGenerators := by
  let H := Subgroup.closure directFlagPCGenerators
  have hpc1 : G2TwoSylowPCAutomorphisms.pc1Aut ∈ H := by
    have hword : pcWord (pcBits true false false false false false) ∈ H :=
      Subgroup.subset_closure (Or.inl rfl)
    simpa only [pcWord_pcBits_0] using hword
  unfold peel0
  change (if (f.1 (basis8 7)).x0 then
      G2TwoSylowPCAutomorphisms.pc1Aut else 1) * f ∈ H
  split
  · exact H.mul_mem hpc1 hf
  · exact hf

theorem peel0_mem_nativeFlagStabilizer
    {f : SplitOctF2Aut}
    (hf : f ∈ nativeFlagStabilizer) :
    peel0 f ∈ nativeFlagStabilizer := by
  have hpc1 : G2TwoSylowPCAutomorphisms.pc1Aut ∈ unipotentSubgroup := by
    have h := pcWord_mem_nativeFlagStabilizer
      (pcBits true false false false false false)
    have h' : G2TwoSylowSubgroup.pcWord
        (pcBits true false false false false false) ∈ unipotentSubgroup :=
      ⟨_, rfl⟩
    simpa only [pcWord_pcBits_0] using h'
  unfold peel0
  change (if (f.1 (basis8 7)).x0 then
      G2TwoSylowPCAutomorphisms.pc1Aut else 1) * f ∈
    nativeFlagStabilizer
  split
  · exact unipotent_mul_mem_nativeFlagStabilizer hpc1 hf
  · simpa using hf

theorem peel1_mem_nativeFlagStabilizer
    {f : SplitOctF2Aut}
    (hf : f ∈ nativeFlagStabilizer) :
    peel1 f ∈ nativeFlagStabilizer := by
  have hpc2 : G2TwoSylowPCAutomorphisms.pc2Aut ∈ unipotentSubgroup := by
    have h : G2TwoSylowSubgroup.pcWord
        (pcBits false true false false false false) ∈ unipotentSubgroup :=
      ⟨_, rfl⟩
    simpa only [pcWord_pcBits_1] using h
  have hfactor : G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut ∈ unipotentSubgroup := by
    rw [← G2TwoSylowPCAutomorphisms.pc2Aut_inv_eq]
    exact unipotentSubgroup.inv_mem hpc2
  unfold peel1
  change (if (f.1 (basis8 2)).x1 then
      G2TwoSylowPCAutomorphisms.pc6Aut *
        G2TwoSylowPCAutomorphisms.pc2Aut else 1) * f ∈
    nativeFlagStabilizer
  split
  · exact unipotent_mul_mem_nativeFlagStabilizer hfactor hf
  · simpa using hf

theorem peel2_mem_nativeFlagStabilizer
    {f : SplitOctF2Aut}
    (hf : f ∈ nativeFlagStabilizer) :
    peel2 f ∈ nativeFlagStabilizer := by
  have hpc3 : G2TwoSylowPCAutomorphisms.pc3Aut ∈ unipotentSubgroup := by
    have h : G2TwoSylowSubgroup.pcWord
        (pcBits false false true false false false) ∈ unipotentSubgroup :=
      ⟨_, rfl⟩
    simpa only [pcWord_pcBits_2] using h
  have hfactor : G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut ∈ unipotentSubgroup := by
    rw [← G2TwoSylowPCAutomorphisms.pc3Aut_inv_eq]
    exact unipotentSubgroup.inv_mem hpc3
  unfold peel2
  change (if (f.1 (basis8 7)).x1 then
      G2TwoSylowPCAutomorphisms.pc6Aut *
        G2TwoSylowPCAutomorphisms.pc3Aut else 1) * f ∈
    nativeFlagStabilizer
  split
  · exact unipotent_mul_mem_nativeFlagStabilizer hfactor hf
  · simpa using hf

theorem peel34_mem_nativeFlagStabilizer
    {f : SplitOctF2Aut}
    (hf : f ∈ nativeFlagStabilizer) :
    peel34 f ∈ nativeFlagStabilizer := by
  have hpc4 : G2TwoSylowPCAutomorphisms.pc4Aut ∈ unipotentSubgroup := by
    rw [← sylowTwoSubgroup_eq_unipotentSubgroup]
    change G2TwoSylowPCAutomorphisms.pcGenerator (3 : Fin 6) ∈
      G2TwoSylowSubgroup.sylowTwoSubgroup
    rcases G2TwoPCConcreteFacts.pcGenerator_mem_pcWord_range (3 : Fin 6) with
      ⟨e, he⟩
    rw [← he]
    exact G2TwoSylowSubgroup.pcWord_mem_sylow e
  have hpc5 : G2TwoSylowPCAutomorphisms.pc5Aut ∈ unipotentSubgroup := by
    have h : G2TwoSylowSubgroup.pcWord
        (pcBits false false false false true false) ∈ unipotentSubgroup :=
      ⟨_, rfl⟩
    simpa only [pcWord_pcBits_4] using h
  unfold peel34
  change (if (f.1 (basis8 2)).y1 then
      G2TwoSylowPCAutomorphisms.pc5Aut else 1) *
      (if (f.1 (basis8 3)).x2 ^^ (f.1 (basis8 2)).y1 then
        G2TwoSylowPCAutomorphisms.pc4Aut else 1) * f ∈
    nativeFlagStabilizer
  split <;> split
  · exact unipotent_mul_mul_mem_nativeFlagStabilizer hpc5 hpc4 hf
  · exact unipotent_mul_mem_nativeFlagStabilizer hpc5 hf
  · exact unipotent_mul_mem_nativeFlagStabilizer hpc4 hf
  · simpa using hf

theorem peel5_mem_nativeFlagStabilizer
    {f : SplitOctF2Aut}
    (hf : f ∈ nativeFlagStabilizer) :
    peel5 f ∈ nativeFlagStabilizer := by
  have hpc6 : G2TwoSylowPCAutomorphisms.pc6Aut ∈ unipotentSubgroup := by
    rw [← sylowTwoSubgroup_eq_unipotentSubgroup]
    exact Subgroup.subset_closure ⟨5, rfl⟩
  unfold peel5
  change (if (f.1 (basis8 2)).x2 then
      G2TwoSylowPCAutomorphisms.pc6Aut else 1) * f ∈
    nativeFlagStabilizer
  split
  · exact unipotent_mul_mem_nativeFlagStabilizer hpc6 hf
  · simpa using hf

theorem peel1_mem_directGeneratorClosure
    {f : SplitOctF2Aut}
    (hf : f ∈ Subgroup.closure directFlagPCGenerators) :
    peel1 f ∈ Subgroup.closure directFlagPCGenerators := by
  let H := Subgroup.closure directFlagPCGenerators
  have hpc2 : G2TwoSylowPCAutomorphisms.pc2Aut ∈ H := by
    have hword : pcWord (pcBits false true false false false false) ∈ H :=
      Subgroup.subset_closure (Or.inr (Or.inl rfl))
    simpa only [pcWord_pcBits_1] using hword
  have hmul : (G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc2Aut) ∈ H := by
    rw [← G2TwoSylowPCAutomorphisms.pc2Aut_inv_eq]
    exact H.inv_mem hpc2
  unfold peel1
  change (if (f.1 (basis8 2)).x1 then
      G2TwoSylowPCAutomorphisms.pc6Aut *
        G2TwoSylowPCAutomorphisms.pc2Aut else 1) * f ∈ H
  split
  · exact H.mul_mem hmul hf
  · simpa using hf

theorem peel2_mem_directGeneratorClosure
    {f : SplitOctF2Aut}
    (hf : f ∈ Subgroup.closure directFlagPCGenerators) :
    peel2 f ∈ Subgroup.closure directFlagPCGenerators := by
  let H := Subgroup.closure directFlagPCGenerators
  have hpc3 : G2TwoSylowPCAutomorphisms.pc3Aut ∈ H := by
    have hword : pcWord (pcBits false false true false false false) ∈ H :=
      Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))
    simpa only [pcWord_pcBits_2] using hword
  have hmul : (G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut) ∈ H := by
    rw [← G2TwoSylowPCAutomorphisms.pc3Aut_inv_eq]
    exact H.inv_mem hpc3
  unfold peel2
  change (if (f.1 (basis8 7)).x1 then
      G2TwoSylowPCAutomorphisms.pc6Aut *
        G2TwoSylowPCAutomorphisms.pc3Aut else 1) * f ∈ H
  split
  · exact H.mul_mem hmul hf
  · simpa using hf

theorem peel34_mem_directGeneratorClosure
    {f : SplitOctF2Aut}
    (hf : f ∈ Subgroup.closure directFlagPCGenerators) :
    peel34 f ∈ Subgroup.closure directFlagPCGenerators := by
  let H := Subgroup.closure directFlagPCGenerators
  have hpc4 : G2TwoSylowPCAutomorphisms.pc4Aut ∈ H := by
    change G2TwoSylowPCAutomorphisms.pc4Aut ∈
      Subgroup.closure directFlagPCGenerators
    rw [directFlagPCGenerators_closure_eq_unipotentSubgroup]
    rw [← sylowTwoSubgroup_eq_unipotentSubgroup]
    change G2TwoSylowPCAutomorphisms.pcGenerator (3 : Fin 6) ∈
      G2TwoSylowSubgroup.sylowTwoSubgroup
    rcases G2TwoPCConcreteFacts.pcGenerator_mem_pcWord_range (3 : Fin 6) with
      ⟨e, he⟩
    rw [← he]
    exact G2TwoSylowSubgroup.pcWord_mem_sylow e
  have hpc5 : G2TwoSylowPCAutomorphisms.pc5Aut ∈ H := by
    change G2TwoSylowPCAutomorphisms.pc5Aut ∈
      Subgroup.closure directFlagPCGenerators
    rw [directFlagPCGenerators_closure_eq_unipotentSubgroup]
    rw [← sylowTwoSubgroup_eq_unipotentSubgroup]
    change G2TwoSylowPCAutomorphisms.pcGenerator (4 : Fin 6) ∈
      G2TwoSylowSubgroup.sylowTwoSubgroup
    rcases G2TwoPCConcreteFacts.pcGenerator_mem_pcWord_range (4 : Fin 6) with
      ⟨e, he⟩
    rw [← he]
    exact G2TwoSylowSubgroup.pcWord_mem_sylow e
  unfold peel34
  dsimp
  split <;> split
  · exact H.mul_mem (H.mul_mem hpc5 hpc4) hf
  · exact H.mul_mem hpc5 hf
  · exact H.mul_mem hpc4 hf
  · simpa using hf

theorem peel5_mem_directGeneratorClosure
    {f : SplitOctF2Aut}
    (hf : f ∈ Subgroup.closure directFlagPCGenerators) :
    peel5 f ∈ Subgroup.closure directFlagPCGenerators := by
  let H := Subgroup.closure directFlagPCGenerators
  have hpc6 : G2TwoSylowPCAutomorphisms.pc6Aut ∈ H := by
    change G2TwoSylowPCAutomorphisms.pc6Aut ∈
      Subgroup.closure directFlagPCGenerators
    rw [directFlagPCGenerators_closure_eq_unipotentSubgroup]
    rw [← sylowTwoSubgroup_eq_unipotentSubgroup]
    exact Subgroup.subset_closure ⟨5, rfl⟩
  unfold peel5
  change (if (f.1 (basis8 2)).x2 then
      G2TwoSylowPCAutomorphisms.pc6Aut else 1) * f ∈ H
  split
  · exact H.mul_mem hpc6 hf
  · simpa using hf

theorem fullPeel_mem_directGeneratorClosure_of_mem
    {g : SplitOctF2Aut}
    (hg : g ∈ Subgroup.closure directFlagPCGenerators) :
    fullPeel g ∈ Subgroup.closure directFlagPCGenerators := by
  have h0 := peel0_mem_directGeneratorClosure hg
  have h1 := peel1_mem_directGeneratorClosure h0
  have h2 := peel2_mem_directGeneratorClosure h1
  have h34 := peel34_mem_directGeneratorClosure h2
  exact peel5_mem_directGeneratorClosure h34

theorem peel34_basis8_seven_fixed_of_pivots
    {f : SplitOctF2Aut}
    (h7 : f.1 (basis8 7) = basis8 7)
    (hy1 : (f.1 (basis8 2)).y1 = false)
    (hx2 : (f.1 (basis8 3)).x2 = false) :
    (peel34 f).1 (basis8 7) = basis8 7 := by
  rw [peel34_basis8_7]
  simp [hy1, hx2, h7]

theorem add_self_cancel (X Y : SplitOctF2) : add X (add X Y) = Y := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  rcases Y with ⟨a',b',x0',x1',x2',y0',y1',y2'⟩
  dsimp [add, add2]
  ext <;> simp

theorem transformedVector_eq_add_basis8_five_seven :
    (⟨false, false, false, false, false, true, false, true⟩ : SplitOctF2) =
      add (basis8 5) (basis8 7) := rfl

theorem automorphism_apply_transformedVector (f : SplitOctF2Aut) :
    f.1 ⟨false, false, false, false, false, true, false, true⟩ =
      add (f.1 (basis8 5)) (f.1 (basis8 7)) := by
  rw [transformedVector_eq_add_basis8_five_seven]
  exact f.2.2.1 (basis8 5) (basis8 7)

theorem automorphism_transformedVector_readback
    (f : SplitOctF2Aut)
    (h5 : f.1 (basis8 5) = basis8 5)
    (h7 : f.1 (basis8 7) = add (basis8 5) (basis8 7)) :
    f.1 ⟨false, false, false, false, false, true, false, true⟩ = basis8 7 := by
  rw [automorphism_apply_transformedVector, h5, h7]
  exact add_self_cancel (basis8 5) (basis8 7)

theorem peel5_basis8_seven_fixed_of_x2_true_readback
    {f : SplitOctF2Aut}
    (hx2 : (f.1 (basis8 2)).x2 = true)
    (hreadback : f.1 ⟨false, false, false, false, false, true, false, true⟩ = basis8 7) :
    (peel5 f).1 (basis8 7) = basis8 7 := by
  rw [peel5_basis8_7_readback, hx2, hreadback]
  simp

theorem peel5_basis8_seven_fixed_iff_of_x2_true
    {f : SplitOctF2Aut}
    (hx2 : (f.1 (basis8 2)).x2 = true) :
    ((peel5 f).1 (basis8 7) = basis8 7 ↔
      f.1 ⟨false, false, false, false, false, true, false, true⟩ = basis8 7) := by
  rw [peel5_basis8_7_readback, hx2]
  rfl

theorem peel5_basis8_seven_fixed_of_branch_readback
    {f : SplitOctF2Aut}
    (hbranch :
      ((f.1 (basis8 2)).x2 = false ∧ f.1 (basis8 7) = basis8 7) ∨
      ((f.1 (basis8 2)).x2 = true ∧
        f.1 ⟨false, false, false, false, false, true, false, true⟩ = basis8 7)) :
    (peel5 f).1 (basis8 7) = basis8 7 := by
  rcases hbranch with hbranch | hbranch
  · exact (peel5_basis8_seven_fixed_of_x2_false hbranch.1).trans hbranch.2
  · exact peel5_basis8_seven_fixed_of_x2_true_readback hbranch.1 hbranch.2

theorem fullPeel_basis8_seven_fixed_of_preceding_readbacks
    {g : SplitOctF2Aut}
    (hx2 : ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).x2 = false)
    (h7 : (peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 7) = basis8 7) :
    (fullPeel g).1 (basis8 7) = basis8 7 := by
  have hstep := peel5_basis8_seven_fixed_of_x2_false
    (f := peel34 (peel2 (peel1 (peel0 g)))) hx2
  simpa [fullPeel] using hstep.trans h7

/-! The final peel is a direct wrapper around the two exact branches above.
    This keeps the remaining obligation local: only the transformed readback
    for the branch selected by `peel34` is needed. -/
theorem fullPeel_basis8_seven_fixed_of_preceding_branch_readback
    {g : SplitOctF2Aut}
    (hbranch :
      (((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).x2 = false ∧
        (peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 7) = basis8 7) ∨
      (((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).x2 = true ∧
        (peel34 (peel2 (peel1 (peel0 g)))).1
          ⟨false, false, false, false, false, true, false, true⟩ = basis8 7)) :
    (fullPeel g).1 (basis8 7) = basis8 7 := by
  simpa [fullPeel] using
    (peel5_basis8_seven_fixed_of_branch_readback
      (f := peel34 (peel2 (peel1 (peel0 g)))) hbranch)

/-! A certificate-shaped assembly boundary for the two peel branches.  The
    hypotheses are native readbacks for the four inputs consumed by `peel34`
    and the additional input consumed by `peel5`; no subgroup or cardinality
    fact is used to manufacture them. -/
theorem fullPeel_basis8_seven_fixed_of_preceding_transformed_readbacks
    {g : SplitOctF2Aut}
    (hA : (peel2 (peel1 (peel0 g))).1
      (add ePlus (add eMinus (add (basis8 4) (basis8 7)))) = basis8 7)
    (hB : (peel2 (peel1 (peel0 g))).1
      (add ePlus (add eMinus (add (basis8 4)
        (add (basis8 6) (basis8 7))))) = basis8 7)
    (hC : (peel2 (peel1 (peel0 g))).1
      (add (basis8 6) (basis8 7)) = basis8 7)
    (hD : (peel2 (peel1 (peel0 g))).1 (basis8 7) = basis8 7)
    (hE : (peel34 (peel2 (peel1 (peel0 g)))).1
      ⟨false, false, false, false, false, true, false, true⟩ = basis8 7) :
    (fullPeel g).1 (basis8 7) = basis8 7 := by
  let f := peel2 (peel1 (peel0 g))
  have h34 : (peel34 f).1 (basis8 7) = basis8 7 := by
    exact peel34_basis8_7_fixed_of_transformed_readbacks hA hB hC hD
  by_cases hx2 : ((peel34 f).1 (basis8 2)).x2 = false
  · exact fullPeel_basis8_seven_fixed_of_preceding_readbacks hx2 h34
  · have hx2' : ((peel34 f).1 (basis8 2)).x2 = true := by
      cases h : ((peel34 f).1 (basis8 2)).x2 <;> simp_all
    apply fullPeel_basis8_seven_fixed_of_preceding_branch_readback
    exact Or.inr ⟨hx2', hE⟩

theorem nativeFlagStabilizer_le_directGeneratorClosure_of_matrix_readback
    (hreadback : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      ∃ e : PCExponent, autMatrix g = pcMatrix e) :
    nativeFlagStabilizer ≤ Subgroup.closure directFlagPCGenerators := by
  intro g hg
  have hU : g ∈ unipotentSubgroup :=
    nativeFlagStabilizer_le_unipotent_of_matrix_readback hreadback hg
  have hclosure : unipotentSubgroup =
      Subgroup.closure directFlagPCGenerators :=
    directFlagPCGenerators_closure_eq_unipotentSubgroup.symm
  rw [← hclosure]
  exact hU

theorem nativeFlagStabilizer_le_directGeneratorClosure_of_fullPeel_mem
    (hpeel : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      fullPeel g ∈ unipotentSubgroup) :
    nativeFlagStabilizer ≤ Subgroup.closure directFlagPCGenerators := by
  intro g hg
  let H := Subgroup.closure directFlagPCGenerators
  have hpc : G2TwoSylowSubgroup.pcWord (extractAllBits g) ∈ H := by
    change G2TwoSylowSubgroup.pcWord (extractAllBits g) ∈
      Subgroup.closure directFlagPCGenerators
    rw [directFlagPCGenerators_closure_eq_unipotentSubgroup]
    exact ⟨extractAllBits g, rfl⟩
  have hres : fullPeel g ∈ H := by
    change fullPeel g ∈ Subgroup.closure directFlagPCGenerators
    rw [directFlagPCGenerators_closure_eq_unipotentSubgroup]
    exact hpeel g hg
  have hfactor := fullPeel_pcWord_factorization g
  rw [← hfactor]
  exact H.mul_mem hpc hres

/-! On the already identified direct-generator closure, the full peel is
    genuinely trivial.  This is deliberately scoped to the closure; it does
    not identify the whole flag stabilizer with that closure. -/
theorem fullPeel_eq_one_of_mem_directGeneratorClosure
    {g : SplitOctF2Aut}
    (hg : g ∈ Subgroup.closure directFlagPCGenerators) :
    fullPeel g = 1 := by
  rw [directFlagPCGenerators_closure_eq_unipotentSubgroup] at hg
  rcases hg with ⟨e, rfl⟩
  exact fullPeel_pcWord_eq_one e

theorem fullPeel_basis8_readback_of_mem_directGeneratorClosure
    {g : SplitOctF2Aut}
    (hg : g ∈ Subgroup.closure directFlagPCGenerators) (j : Fin 8) :
    (fullPeel g).1 (basis8 j) = basis8 j := by
  rw [fullPeel_eq_one_of_mem_directGeneratorClosure hg]
  rfl

theorem fullPeel_mem_unipotent_of_basis_readback
    {g : SplitOctF2Aut}
    (hreadback : ∀ j : Fin 8,
      (fullPeel g).1 (basis8 j) = basis8 j) :
    fullPeel g ∈ unipotentSubgroup := by
  apply mem_unipotentSubgroup_of_basis_action_eq
    (e := fun _ : Fin 6 => false)
  intro j
  simpa [pcWord_zero_eq_one] using hreadback j

theorem nativeFlagStabilizer_mem_directGeneratorClosure_of_basis_readback
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (hreadback : ∀ j : Fin 8,
      (fullPeel g).1 (basis8 j) = basis8 j) :
    g ∈ Subgroup.closure directFlagPCGenerators := by
  obtain ⟨e, heq, _⟩ :=
    nativeFlagStabilizer_pcWord_residual_decomposition hg
  let H := Subgroup.closure directFlagPCGenerators
  have hpc : G2TwoSylowSubgroup.pcWord e ∈ H := by
    change G2TwoSylowSubgroup.pcWord e ∈
      Subgroup.closure directFlagPCGenerators
    rw [directFlagPCGenerators_closure_eq_unipotentSubgroup]
    exact ⟨e, rfl⟩
  have hres : fullPeel g ∈ H := by
    change fullPeel g ∈ Subgroup.closure directFlagPCGenerators
    rw [directFlagPCGenerators_closure_eq_unipotentSubgroup]
    exact fullPeel_mem_unipotent_of_basis_readback hreadback
  rw [heq]
  exact H.mul_mem hpc hres

theorem fullPeel_basis8_four_readback
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    (fullPeel g).1 (basis8 4) = basis8 4 := by
  exact nativeFlagStabilizer_basis8_four
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)

theorem fullPeel_basis8_fifth_readback
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    (fullPeel g).1 (basis8 5) = basis8 5 ∨
      (fullPeel g).1 (basis8 5) = add (basis8 4) (basis8 5) := by
  exact nativeFlagStabilizer_basis8_fifth_cases
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)

theorem fullPeel_basis8_two_x2_readback
    {g : SplitOctF2Aut} :
    ((fullPeel g).1 (basis8 2)).x2 =
      if ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).x2 then
        ((peel34 (peel2 (peel1 (peel0 g)))).1
          (add (basis8 2) (basis8 4))).x2
      else
        ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).x2 := by
  exact peel5_basis8_2_x2
    (peel34 (peel2 (peel1 (peel0 g))))

theorem fullPeel_basis8_two_y1_readback
    {g : SplitOctF2Aut} :
    ((fullPeel g).1 (basis8 2)).y1 =
      if ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).x2 then
        ((peel34 (peel2 (peel1 (peel0 g)))).1
          (add (basis8 2) (basis8 4))).y1
      else
        ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).y1 := by
  rw [fullPeel_basis8_2_formula]
  split <;> rfl

theorem fullPeel_basis8_two_x1_readback
    {g : SplitOctF2Aut} :
    ((fullPeel g).1 (basis8 2)).x1 =
      if ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).x2 then
        ((peel34 (peel2 (peel1 (peel0 g)))).1
          (add (basis8 2) (basis8 4))).x1
      else
        ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).x1 := by
  rw [fullPeel_basis8_2_formula]
  split <;> rfl

/-! The final peel preserves the preceding residual's `x₁` readback in the
    inactive branch.  This small assembly lemma records exactly the
    hypotheses needed for the reduced-shape bridge; it does not infer either
    residual pivot from stabilizer membership. -/
theorem fullPeel_basis8_two_x1_false_of_preceding_readbacks
    {g : SplitOctF2Aut}
    (hx2 :
      ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).x2 = false)
    (hx1 :
      ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).x1 = false) :
    ((fullPeel g).1 (basis8 2)).x1 = false := by
  rw [fullPeel_basis8_two_x1_readback, hx2, hx1]
  simp

theorem pc6_basis8_six_y0_readback :
    (G2TwoSylowPCAutomorphisms.pc6Aut.1 (basis8 6)).y0 = false := by
  change (G2TwoSylowPCGenerators.pc6Fun (basis8 6)).y0 = false
  simp [G2TwoSylowPCGenerators.pc6Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

theorem pc6_basis8_six_readback :
    G2TwoSylowPCAutomorphisms.pc6Aut.1 (basis8 6) = basis8 6 := by
  change G2TwoSylowPCGenerators.pc6Fun (basis8 6) = basis8 6
  ext <;> simp [G2TwoSylowPCGenerators.pc6Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

theorem peel5_basis8_six_y0_readback (f : SplitOctF2Aut) :
    ((peel5 f).1 (basis8 6)).y0 = (f.1 (basis8 6)).y0 := by
  dsimp [peel5]
  split
  · rw [automorphism_mul_apply, pc6_basis8_six_readback]
  · rfl

theorem peel0_basis8_six_y0_readback (f : SplitOctF2Aut) :
    ((peel0 f).1 (basis8 6)).y0 = (f.1 (basis8 6)).y0 := by
  rw [peel0_apply_basis8_6]

theorem fullPeel_basis8_six_y0_eq_peel2_residual
    (g : SplitOctF2Aut) :
    ((fullPeel g).1 (basis8 6)).y0 =
      ((peel2 (peel1 (peel0 g))).1 (basis8 6)).y0 := by
  let q := peel2 (peel1 (peel0 g))
  calc
    ((fullPeel g).1 (basis8 6)).y0 = ((peel34 q).1 (basis8 6)).y0 := by
      simpa [fullPeel, q] using peel5_basis8_six_y0_readback (peel34 q)
    _ = (q.1 (basis8 6)).y0 := by rw [peel34_basis8_6]
    _ = ((peel2 (peel1 (peel0 g))).1 (basis8 6)).y0 := by rfl

theorem pc6pc3_basis8_six_readback :
    (G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 6) =
      ⟨false, false, false, false, true, false, true, false⟩ := by
  change G2TwoSylowPCGenerators.pc3Fun
    (G2TwoSylowPCGenerators.pc6Fun (basis8 6)) = _
  ext <;> simp [G2TwoSylowPCGenerators.pc3Fun,
    G2TwoSylowPCGenerators.pc6Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

theorem fullPeel_basis8_two_y0_readback
    {g : SplitOctF2Aut} :
    ((fullPeel g).1 (basis8 2)).y0 =
      if ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).x2 then
        ((peel34 (peel2 (peel1 (peel0 g)))).1
          (add (basis8 2) (basis8 4))).y0
      else
        ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).y0 := by
  rw [fullPeel_basis8_2_formula]
  split <;> rfl

theorem peel5_basis8_two_eq_of_basis_readbacks
    {f : SplitOctF2Aut}
    (h2 : f.1 (basis8 2) = basis8 2)
    (h4 : f.1 (basis8 4) = basis8 4) :
    (peel5 f).1 (basis8 2) =
        if (f.1 (basis8 2)).x2 then
          add (basis8 2) (basis8 4)
        else basis8 2 := by
  rw [peel5_basis8_2]
  split
  · calc
      f.1 (add (basis8 2) (basis8 4)) =
          add (f.1 (basis8 2)) (f.1 (basis8 4)) :=
        f.2.2.1 (basis8 2) (basis8 4)
      _ = add (basis8 2) (basis8 4) := by rw [h2, h4]
  · exact h2

theorem peel5_basis8_two_fixed_of_basis_readbacks
    {f : SplitOctF2Aut}
    (h2 : f.1 (basis8 2) = basis8 2)
    (h4 : f.1 (basis8 4) = basis8 4) :
    (peel5 f).1 (basis8 2) = basis8 2 := by
  rw [peel5_basis8_two_eq_of_basis_readbacks h2 h4]
  rw [h2]
  simp [basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

theorem fullPeel_basis8_two_fixed_of_preceding_readbacks
    {g : SplitOctF2Aut}
    (h2 : (peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2) = basis8 2)
    (h4 : (peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 4) = basis8 4) :
    (fullPeel g).1 (basis8 2) = basis8 2 := by
  unfold fullPeel
  exact peel5_basis8_two_fixed_of_basis_readbacks h2 h4

theorem fullPeel_basis8_four_fixed_of_preceding_readback
    {g : SplitOctF2Aut}
    (h4 : (peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 4) = basis8 4) :
    (fullPeel g).1 (basis8 4) = basis8 4 := by
  unfold fullPeel
  rw [peel5_basis8_4, h4]

theorem peel34_basis8_four_fixed_of_readback
    {f : SplitOctF2Aut}
    (hf : f.1 (basis8 4) = basis8 4) :
    (peel34 f).1 (basis8 4) = basis8 4 := by
  rw [peel34_basis8_4, hf]

theorem preceding_peel34_basis8_four_readback
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 4) = basis8 4 := by
  have h0 : (peel0 g).1 (basis8 4) = basis8 4 := by
    rw [peel0_apply_basis8_4]
    exact nativeFlagStabilizer_basis8_four hg
  have h1 : (peel1 (peel0 g)).1 (basis8 4) = basis8 4 := by
    rw [peel1_basis8_4, h0]
    simp [basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]
  have h2 : (peel2 (peel1 (peel0 g))).1 (basis8 4) = basis8 4 := by
    rw [peel2_basis8_4, h1]
    simp [basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]
  exact peel34_basis8_four_fixed_of_readback h2

theorem preceding_peel0_basis8_five_readback
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (peel0 g).1 (basis8 5) = basis8 5 := by
  rw [peel0_apply_basis8_5]
  have hcases := nativeFlagStabilizer_basis8_seven_x0_iff_fifth_cases hg
  rcases hcases with ⟨hx0, h5⟩ | ⟨hx0, h5⟩
  · simp [hx0, h5]
  · simp [hx0]
    rw [g.2.2.1, nativeFlagStabilizer_basis8_four hg, h5]
    exact add_self_cancel (basis8 4) (basis8 5)

theorem fullPeel_basis8_five_readback
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (fullPeel g).1 (basis8 5) = basis8 5 := by
  rw [fullPeel_basis8_5_eq_peel0]
  exact preceding_peel0_basis8_five_readback hg

theorem fullPeel_basis8_two_x2
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 2)).x2 = false := by
  unfold fullPeel
  exact peel5_basis8_2_x2_of_basis8_4_fixed
    (preceding_peel34_basis8_four_readback hg)

theorem peel34_basis8_two_fixed_of_readback
    {f : SplitOctF2Aut}
    (hf : f.1 (basis8 2) = basis8 2) :
    (peel34 f).1 (basis8 2) = basis8 2 := by
  rw [peel34_basis8_2, hf]
  simp [basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

theorem peel0_basis8_two_fixed (f : SplitOctF2Aut) :
    (peel0 f).1 (basis8 2) = f.1 (basis8 2) := by
  dsimp [peel0]
  split
  · rw [automorphism_mul_apply, pc1Aut_basis8_2]
  · simp

theorem peel1_basis8_two_fixed_of_readback
    {f : SplitOctF2Aut}
    (hf : f.1 (basis8 2) = basis8 2) :
    (peel1 f).1 (basis8 2) = basis8 2 := by
  rw [peel1_basis8_2, hf]
  simp [basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]

theorem peel2_basis8_two_fixed_of_readback
    {f : SplitOctF2Aut}
    (h2 : f.1 (basis8 2) = basis8 2)
    (h7 : (f.1 (basis8 7)).x1 = false) :
    (peel2 f).1 (basis8 2) = basis8 2 := by
  rw [peel2_basis8_2, h7]
  simp [h2]

theorem preceding_peel34_basis8_two_readback
    {g : SplitOctF2Aut}
    (h2 : g.1 (basis8 2) = basis8 2)
    (h7 : ((peel1 (peel0 g)).1 (basis8 7)).x1 = false) :
    (peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2) = basis8 2 := by
  have h0 : (peel0 g).1 (basis8 2) = basis8 2 := by
    rw [peel0_basis8_two_fixed, h2]
  have h1 : (peel1 (peel0 g)).1 (basis8 2) = basis8 2 := by
    exact peel1_basis8_two_fixed_of_readback h0
  have h2' : (peel2 (peel1 (peel0 g))).1 (basis8 2) = basis8 2 := by
    exact peel2_basis8_two_fixed_of_readback h1 h7
  exact peel34_basis8_two_fixed_of_readback h2'

/-! The preceding residual is not assumed to fix `basis8 2`.  These two
coordinate formulas expose the actual pivots consumed by `peel34`; in
particular, the independent `y2` constraint on a stabilizer element is not
silently substituted for either of them. -/
theorem nativeFlagStabilizer_preceding_y1_x2_control
    {g : SplitOctF2Aut}
    (_hg : g ∈ nativeFlagStabilizer) :
    let f := peel1 (peel0 g)
    let q := peel2 f
    (((q.1 (basis8 2)).y1 =
        if (f.1 (basis8 7)).x1 then
          (f.1 (add ePlus (add eMinus (add (basis8 2)
            (add (basis8 4) (add (basis8 5) (basis8 6))))))).y1
        else (f.1 (basis8 2)).y1) ∧
      ((q.1 (basis8 2)).x2 =
        if (f.1 (basis8 7)).x1 then
          (f.1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
            G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 2))).x2
        else (f.1 (basis8 2)).x2)) := by
  dsimp
  constructor
  · exact peel2_basis8_2_y1 (peel1 (peel0 g))
  · rw [peel2_basis8_2]
    split <;> rfl

/-! Exact composite readback for the pivot vector.  This is deliberately a
    formula, not a fixed-point claim: the remaining stabilizer argument must
    prove that the selected branches evaluate to `basis8 7`. -/
theorem preceding_peel2_basis8_seven_readback_formula
    (g : SplitOctF2Aut) :
    (peel2 (peel1 (peel0 g))).1 (basis8 7) =
      if ((peel1 (peel0 g)).1 (basis8 7)).x1 then
        (peel1 (peel0 g)).1
          (add ePlus (add eMinus (add (basis8 3)
            (add (basis8 6) (basis8 7)))))
      else
        (peel1 (peel0 g)).1 (basis8 7) := by
  exact peel2_basis8_7_readback (peel1 (peel0 g))

/-! The active `peel2` input is the image of an explicit native vector.  This
projection exposes its five summands before any stabilizer-specific
coordinate argument is attempted. -/
theorem automorphism_pc6pc3_basis8_seven_expansion
    (f : SplitOctF2Aut) :
    f.1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 7)) =
      add (f.1 ePlus) (add (f.1 eMinus) (add (f.1 (basis8 3))
        (add (f.1 (basis8 6)) (f.1 (basis8 7))))) := by
  rw [pc6pc3_basis8_7]
  rw [automorphism_map_add, automorphism_map_add,
    automorphism_map_add, automorphism_map_add]

theorem automorphism_pc6pc3_basis8_seven_y2_projection
    (f : SplitOctF2Aut) :
    (f.1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 7))).y2 =
      (add (f.1 ePlus) (add (f.1 eMinus) (add (f.1 (basis8 3))
        (add (f.1 (basis8 6)) (f.1 (basis8 7)))))).y2 := by
  have h := automorphism_pc6pc3_basis8_seven_expansion f
  exact congrArg SplitOctF2.y2 h

theorem automorphism_pc6pc3_basis8_seven_x0_projection
    (f : SplitOctF2Aut) :
    (f.1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 7))).x0 =
      (add (f.1 ePlus) (add (f.1 eMinus) (add (f.1 (basis8 3))
        (add (f.1 (basis8 6)) (f.1 (basis8 7)))))).x0 := by
  have h := automorphism_pc6pc3_basis8_seven_expansion f
  exact congrArg SplitOctF2.x0 h

theorem automorphism_ePlus_add_eMinus
    (f : SplitOctF2Aut) :
    f.1 (add ePlus eMinus) = one := by
  rw [ePlus_add_eMinus_eq_one]
  exact f.2.1

theorem automorphism_pc6pc3_basis8_seven_unit_reduced
    (f : SplitOctF2Aut) :
    f.1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 7)) =
      add one (add (f.1 (basis8 3))
        (add (f.1 (basis8 6)) (f.1 (basis8 7)))) := by
  calc
    f.1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
        G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 7)) =
        add (f.1 ePlus) (add (f.1 eMinus) (add (f.1 (basis8 3))
          (add (f.1 (basis8 6)) (f.1 (basis8 7))))) :=
      automorphism_pc6pc3_basis8_seven_expansion f
    _ = add (add (f.1 ePlus) (f.1 eMinus))
        (add (f.1 (basis8 3))
          (add (f.1 (basis8 6)) (f.1 (basis8 7)))) := by
      rw [InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.add_assoc]
    _ = add one (add (f.1 (basis8 3))
        (add (f.1 (basis8 6)) (f.1 (basis8 7)))) := by
      rw [← automorphism_map_add, ePlus_add_eMinus_eq_one, f.2.1]

theorem nativeFlagStabilizer_pc6pc3_basis8_seven_y2
    {f : SplitOctF2Aut}
    (hf : f ∈ nativeFlagStabilizer) :
    (f.1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 7))).y2 = true := by
  have hred := automorphism_pc6pc3_basis8_seven_unit_reduced f
  have h3 := nativeFlagStabilizer_basis8_three_y2_zero hf
  have h6 := nativeFlagStabilizer_basis8_six_coordinate_form hf
  have h6y2 : (f.1 (basis8 6)).y2 = false := by
    have h := congrArg SplitOctF2.y2 h6
    simpa [h6] using h
  have h7 := nativeFlagStabilizer_basis8_seven_y2 hf
  have hone : (one : SplitOctF2).y2 = false := rfl
  rw [hred]
  simp only [add]
  simp [h3, h6y2, h7, hone, add2]

theorem nativeFlagStabilizer_peel2_basis8_seven_y2_of_active
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (hx1 : ((peel1 (peel0 g)).1 (basis8 7)).x1 = true) :
    ((peel2 (peel1 (peel0 g))).1 (basis8 7)).y2 = true := by
  have h0 := peel0_mem_nativeFlagStabilizer hg
  have h1 := peel1_mem_nativeFlagStabilizer h0
  rw [peel2_basis8_7_readback, hx1]
  exact nativeFlagStabilizer_pc6pc3_basis8_seven_y2 h1

/-! The inactive `peel2` branch leaves the current image unchanged, while
    the active branch has the exact native `pc6 * pc3` readback above. -/
theorem nativeFlagStabilizer_peel2_basis8_seven_y2_readback
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((peel2 (peel1 (peel0 g))).1 (basis8 7)).y2 = true := by
  have h0 := peel0_mem_nativeFlagStabilizer hg
  have h1 := peel1_mem_nativeFlagStabilizer h0
  by_cases hx1 : ((peel1 (peel0 g)).1 (basis8 7)).x1 = true
  · exact nativeFlagStabilizer_peel2_basis8_seven_y2_of_active hg hx1
  · have hx1' : ((peel1 (peel0 g)).1 (basis8 7)).x1 = false := by
      cases h : ((peel1 (peel0 g)).1 (basis8 7)).x1 <;> simp_all
    rw [peel2_basis8_7_readback, hx1']
    simpa using nativeFlagStabilizer_basis8_seven_y2 h1

theorem peel34_basis8_seven_y2_of_readbacks
    {f : SplitOctF2Aut}
    (h4 : f.1 (basis8 4) = basis8 4)
    (h6y2 : (f.1 (basis8 6)).y2 = false)
    (h7y2 : (f.1 (basis8 7)).y2 = true) :
    ((peel34 f).1 (basis8 7)).y2 = true := by
  rw [peel34_basis8_7]
  dsimp
  split <;> split
  · rw [automorphism_map_ePlus_eMinus_basis8_4_basis8_7, h4]
    simp [h7y2, add, add2] <;> rfl
  · rw [automorphism_map_ePlus_eMinus_basis8_4_basis8_6_basis8_7, h4]
    simp [h6y2, h7y2, add, add2] <;> rfl
  · rw [automorphism_map_add]
    simp [h6y2, h7y2, add, add2]
  · exact h7y2

theorem nativeFlagStabilizer_peel34_basis8_seven_y2_readback
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 7)).y2 = true := by
  have h0 := peel0_mem_nativeFlagStabilizer hg
  have h1 := peel1_mem_nativeFlagStabilizer h0
  have h2 := peel2_mem_nativeFlagStabilizer h1
  apply peel34_basis8_seven_y2_of_readbacks
  · have h4₀ : (peel0 g).1 (basis8 4) = basis8 4 := by
      rw [peel0_apply_basis8_4]
      exact nativeFlagStabilizer_basis8_four hg
    have h4₁ : (peel1 (peel0 g)).1 (basis8 4) = basis8 4 := by
      rw [peel1_basis8_4, h4₀]
      simp [basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]
    rw [peel2_basis8_4, h4₁]
    simp [basis8, ePlus, eMinus, up0, up1, up2, down0, down1, down2]
  · have h6 := nativeFlagStabilizer_basis8_six_coordinate_form h2
    have hy2 := congrArg SplitOctF2.y2 h6
    simpa [h6] using hy2
  · exact nativeFlagStabilizer_peel2_basis8_seven_y2_readback hg

theorem fullPeel_basis8_seven_y2_of_preceding_x2_false
    {g : SplitOctF2Aut}
    (h7y2 :
      ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 7)).y2 = true)
    (hx2 :
      ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).x2 = false) :
    ((fullPeel g).1 (basis8 7)).y2 = true := by
  rw [fullPeel, peel5_basis8_7_readback, hx2]
  exact h7y2

theorem fullPeel_basis8_seven_y2_of_preceding_x2_true
    {g : SplitOctF2Aut}
    (hx2 :
      ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2)).x2 = true)
    (hreadback :
      (peel34 (peel2 (peel1 (peel0 g)))).1
        ⟨false, false, false, false, false, true, false, true⟩ = basis8 7) :
    ((fullPeel g).1 (basis8 7)).y2 = true := by
  have hfix := peel5_basis8_seven_fixed_of_x2_true_readback hx2 hreadback
  have hfull : (fullPeel g).1 (basis8 7) = basis8 7 := by
    simpa [fullPeel] using hfix
  rw [hfull]
  rfl

theorem active_basis8_seven_vector_eq_basis8_fifth_add_seventh :
    (⟨false, false, false, false, false, true, false, true⟩ : SplitOctF2) =
      add (basis8 5) (basis8 7) := by
  rfl

theorem automorphism_active_basis8_seven_vector
    (f : SplitOctF2Aut) :
    f.1 ⟨false, false, false, false, false, true, false, true⟩ =
      add (f.1 (basis8 5)) (f.1 (basis8 7)) := by
  rw [active_basis8_seven_vector_eq_basis8_fifth_add_seventh]
  exact f.2.2.1 _ _

theorem automorphism_active_basis8_seven_vector_y2_of_readbacks
    {f : SplitOctF2Aut}
    (h5y2 : (f.1 (basis8 5)).y2 = false)
    (h7y2 : (f.1 (basis8 7)).y2 = true) :
    (f.1 ⟨false, false, false, false, false, true, false, true⟩).y2 = true := by
  rw [automorphism_active_basis8_seven_vector]
  simp [h5y2, h7y2, add, add2]

theorem fullPeel_basis8_seven_y2_of_stabilizer
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 7)).y2 = true := by
  let f := peel34 (peel2 (peel1 (peel0 g)))
  have hf : f ∈ nativeFlagStabilizer := by
    dsimp [f]
    exact peel34_mem_nativeFlagStabilizer
      (peel2_mem_nativeFlagStabilizer
        (peel1_mem_nativeFlagStabilizer (peel0_mem_nativeFlagStabilizer hg)))
  have h7y2 : (f.1 (basis8 7)).y2 = true := by
    exact nativeFlagStabilizer_peel34_basis8_seven_y2_readback hg
  have h5y2 : (f.1 (basis8 5)).y2 = false := by
    rcases nativeFlagStabilizer_basis8_fifth_cases hf with h5 | h5
    · rw [h5]
      rfl
    · rw [h5]
      rfl
  by_cases hx2 : (f.1 (basis8 2)).x2 = false
  · exact fullPeel_basis8_seven_y2_of_preceding_x2_false h7y2 hx2
  · have hx2' : (f.1 (basis8 2)).x2 = true := by
      cases h : (f.1 (basis8 2)).x2 <;> simp_all
    rw [fullPeel, peel5_basis8_7_readback, hx2']
    exact automorphism_active_basis8_seven_vector_y2_of_readbacks
      h5y2 h7y2

theorem fullPeel_basis8_seven_x0_false
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 7)).x0 = false := by
  have hx0 := nativeFlagStabilizer_basis8_seven_x0_eq_basis8_fifth_x2
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)
  rw [fullPeel_basis8_five_readback hg] at hx0
  exact hx0

theorem fullPeel_basis8_fifth_fixed
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    (fullPeel g).1 (basis8 5) = basis8 5 := by
  rcases fullPeel_basis8_fifth_readback hg with h5 | h5
  · exact h5
  · have hx0 := fullPeel_basis8_seven_x0_false hg
    have hrel := nativeFlagStabilizer_basis8_seven_x0_eq_basis8_fifth_x2
      (fullPeel_mem_nativeFlagStabilizer_of_mem hg)
    rw [hx0] at hrel
    rw [h5] at hrel
    simpa [basis8, add, add2] using hrel

theorem fullPeel_basis8_seven_square_zero
    {g : SplitOctF2Aut} :
    mul ((fullPeel g).1 (basis8 7)) ((fullPeel g).1 (basis8 7)) = zero := by
  calc
    mul ((fullPeel g).1 (basis8 7)) ((fullPeel g).1 (basis8 7)) =
        (fullPeel g).1 (mul (basis8 7) (basis8 7)) :=
      ((fullPeel g).2.2.2 (basis8 7) (basis8 7)).symm
    _ = (fullPeel g).1 zero := by rfl
    _ = zero :=
      InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.automorphism_map_zero
        (fullPeel g)

theorem fullPeel_basis8_seven_square_zero_a
    {g : SplitOctF2Aut} :
    (mul ((fullPeel g).1 (basis8 7)) ((fullPeel g).1 (basis8 7))).a = false := by
  have hsq := fullPeel_basis8_seven_square_zero (g := g)
  rw [hsq]
  rfl

theorem splitOct_basis8_seven_shape_square_y2
    (a b x1 x2 y0 y1 : F2Bit) :
    (mul (⟨a, b, false, x1, x2, y0, y1, true⟩ : SplitOctF2)
      (⟨a, b, false, x1, x2, y0, y1, true⟩ : SplitOctF2)).y2 =
      Bool.xor b a := by
  simp [mul, dot3, cross0, cross1, cross2, add2, mul2]

theorem splitOct_basis8_seven_shape_square_y2_of_trace
    (a b x1 x2 y0 y1 : F2Bit)
    (hab : a = b) :
    (mul (⟨a, b, false, x1, x2, y0, y1, true⟩ : SplitOctF2)
      (⟨a, b, false, x1, x2, y0, y1, true⟩ : SplitOctF2)).y2 = false := by
  rw [splitOct_basis8_seven_shape_square_y2]
  simp [hab]

theorem splitOct_basis8_seven_shape_square_a
    (a b x1 x2 y0 y1 : F2Bit) :
    (mul (⟨a, b, false, x1, x2, y0, y1, true⟩ : SplitOctF2)
      (⟨a, b, false, x1, x2, y0, y1, true⟩ : SplitOctF2)).a =
      Bool.xor (Bool.xor a (x1 && y1)) x2 := by
  simp [mul, dot3, cross0, cross1, cross2, add2, mul2]

theorem splitOct_basis8_seven_shape_square_b
    (a b x1 x2 y0 y1 : F2Bit) :
    (mul (⟨a, b, false, x1, x2, y0, y1, true⟩ : SplitOctF2)
      (⟨a, b, false, x1, x2, y0, y1, true⟩ : SplitOctF2)).b =
      Bool.xor (Bool.xor b (x1 && y1)) x2 := by
  simp [mul, dot3, cross0, cross1, cross2, add2, mul2]
  cases x1 <;> cases y1 <;> rfl

theorem splitOct_basis8_seven_shape_square_a_zero_iff_x2
    (a b x1 x2 y0 y1 : F2Bit)
    (hab : a = b) :
    (mul (⟨a, b, false, x1, x2, y0, y1, true⟩ : SplitOctF2)
      (⟨a, b, false, x1, x2, y0, y1, true⟩ : SplitOctF2)).a = false ↔
      x2 = Bool.xor a (x1 && y1) := by
  rw [splitOct_basis8_seven_shape_square_a]
  cases a <;> cases x1 <;> cases y1 <;> cases x2 <;> simp_all

theorem fullPeel_basis8_seven_partial_shape
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ∃ a b x1 x2 y0 y1 : F2Bit,
      (fullPeel g).1 (basis8 7) =
        ⟨a, b, false, x1, x2, y0, y1, true⟩ ∧
      a = b := by
  let X := (fullPeel g).1 (basis8 7)
  have hx0 : X.x0 = false := fullPeel_basis8_seven_x0_false hg
  have hy2 : X.y2 = true := fullPeel_basis8_seven_y2_of_stabilizer hg
  have htrace : X.a = X.b :=
    nativeFlagStabilizer_basis8_seven_trace_zero
      (fullPeel_mem_nativeFlagStabilizer_of_mem hg)
  refine ⟨X.a, X.b, X.x1, X.x2, X.y0, X.y1, ?_, ?_⟩
  · change X = (⟨X.a, X.b, false, X.x1, X.x2, X.y0, X.y1, true⟩ : SplitOctF2)
    rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
    change x0 = false at hx0
    change y2 = true at hy2
    change a = b at htrace
    subst x0
    subst y2
    rfl
  · exact htrace

theorem fullPeel_basis8_seven_square_zero_y2
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (mul ((fullPeel g).1 (basis8 7)) ((fullPeel g).1 (basis8 7))).y2 = false := by
  rcases fullPeel_basis8_seven_partial_shape hg with
    ⟨a, b, x1, x2, y0, y1, hshape, hab⟩
  rw [hshape]
  exact splitOct_basis8_seven_shape_square_y2_of_trace a b x1 x2 y0 y1 hab

theorem fullPeel_basis8_seven_partial_square_certificate
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ∃ a b x1 x2 y0 y1 : F2Bit,
      (fullPeel g).1 (basis8 7) =
        ⟨a, b, false, x1, x2, y0, y1, true⟩ ∧
      a = b ∧
      (mul ((fullPeel g).1 (basis8 7))
        ((fullPeel g).1 (basis8 7))).a = false := by
  rcases fullPeel_basis8_seven_partial_shape hg with
    ⟨a, b, x1, x2, y0, y1, hshape, hab⟩
  exact ⟨a, b, x1, x2, y0, y1, hshape, hab,
    fullPeel_basis8_seven_square_zero_a⟩

theorem fullPeel_basis8_seven_square_a_coordinate_certificate
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ∃ a b x1 x2 y0 y1 : F2Bit,
      a = b ∧ Bool.xor (Bool.xor a (x1 && y1)) x2 = false := by
  rcases fullPeel_basis8_seven_partial_shape hg with
    ⟨a, b, x1, x2, y0, y1, hshape, hab⟩
  refine ⟨a, b, x1, x2, y0, y1, hab, ?_⟩
  have hsq := fullPeel_basis8_seven_square_zero_a (g := g)
  rw [hshape, splitOct_basis8_seven_shape_square_a] at hsq
  exact hsq

theorem fullPeel_basis8_seven_x2_residual_formula
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ∃ a x1 x2 y0 y1 : F2Bit,
      (fullPeel g).1 (basis8 7) =
        ⟨a, a, false, x1, x2, y0, y1, true⟩ ∧
      x2 = Bool.xor a (x1 && y1) := by
  rcases fullPeel_basis8_seven_partial_shape hg with
    ⟨a, b, x1, x2, y0, y1, hshape, hab⟩
  refine ⟨a, x1, x2, y0, y1, ?_, ?_⟩
  · rw [hshape, hab]
  · have hsq := fullPeel_basis8_seven_square_zero_a (g := g)
    rw [hshape, splitOct_basis8_seven_shape_square_a] at hsq
    cases a <;> cases x1 <;> cases y1 <;> cases x2 <;> simp_all

theorem fullPeel_basis8_seven_x2_eq_boolean_residual
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 7)).x2 =
      Bool.xor ((fullPeel g).1 (basis8 7)).a
        (((fullPeel g).1 (basis8 7)).x1 &&
          ((fullPeel g).1 (basis8 7)).y1) := by
  rcases fullPeel_basis8_seven_x2_residual_formula hg with
    ⟨a, x1, x2, y0, y1, hshape, hx2⟩
  simpa [hshape] using hx2

theorem fullPeel_basis8_seven_x2_false_of_a_x1_false
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (ha : ((fullPeel g).1 (basis8 7)).a = false)
    (hx1 : ((fullPeel g).1 (basis8 7)).x1 = false) :
    ((fullPeel g).1 (basis8 7)).x2 = false := by
  rw [fullPeel_basis8_seven_x2_eq_boolean_residual hg, ha, hx1]
  rfl

theorem fullPeel_basis8_seven_x2_eq_a_of_x1_false
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (hx1 : ((fullPeel g).1 (basis8 7)).x1 = false) :
    ((fullPeel g).1 (basis8 7)).x2 =
      ((fullPeel g).1 (basis8 7)).a := by
  rw [fullPeel_basis8_seven_x2_eq_boolean_residual hg, hx1]
  simp

theorem fullPeel_basis8_seven_x2_false_iff_residual_coordinates
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 7)).x2 = false ↔
      ((fullPeel g).1 (basis8 7)).a =
        (((fullPeel g).1 (basis8 7)).x1 &&
          ((fullPeel g).1 (basis8 7)).y1) := by
  rw [fullPeel_basis8_seven_x2_eq_boolean_residual hg]
  cases hA : ((fullPeel g).1 (basis8 7)).a <;>
    cases hX : ((fullPeel g).1 (basis8 7)).x1 <;>
    cases hY : ((fullPeel g).1 (basis8 7)).y1 <;>
    cases h2 : ((fullPeel g).1 (basis8 7)).x2 <;>
    simp_all

theorem nativeFlagStabilizer_peel34_basis8_two_x2_coordinate_control
    {f : SplitOctF2Aut}
    (hf : f ∈ nativeFlagStabilizer) :
    ((peel34 f).1 (basis8 2)).x2 =
      if (f.1 (basis8 2)).y1 then
        (f.1 (basis8 2)).x2 ^^ (f.1 (basis8 2)).b
      else (f.1 (basis8 2)).x2 := by
  rw [peel34_basis8_2_x2]
  split
  · rw [automorphism_map_add]
    change ((f.1 (basis8 2)).x2 ^^ (f.1 (basis8 6)).x2) = _
    have h6 := nativeFlagStabilizer_basis8_six_coordinate_form hf
    rw [h6]
  · rfl

theorem nativeFlagStabilizer_peel34_basis8_two_y1_coordinate_control
    {f : SplitOctF2Aut}
    (hf : f ∈ nativeFlagStabilizer) :
    ((peel34 f).1 (basis8 2)).y1 =
      if (f.1 (basis8 2)).y1 then
        (f.1 (basis8 2)).y1 ^^ (f.1 (basis8 2)).x0
      else (f.1 (basis8 2)).y1 := by
  rw [peel34_basis8_2_y1]
  split
  · rw [automorphism_map_add]
    change ((f.1 (basis8 2)).y1 ^^ (f.1 (basis8 6)).y1) = _
    have h6 := nativeFlagStabilizer_basis8_six_coordinate_form hf
    rw [h6]
  · rfl

theorem nativeFlagStabilizer_preceding_peel34_basis8_two_coordinate_control
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    let f := peel2 (peel1 (peel0 g))
    (((peel34 f).1 (basis8 2)).x2 =
        if (f.1 (basis8 2)).y1 then
          (f.1 (basis8 2)).x2 ^^ (f.1 (basis8 2)).b
        else (f.1 (basis8 2)).x2) ∧
      ((peel34 f).1 (basis8 2)).y1 =
        if (f.1 (basis8 2)).y1 then
          (f.1 (basis8 2)).y1 ^^ (f.1 (basis8 2)).x0
        else (f.1 (basis8 2)).y1 := by
  dsimp
  have h0 := peel0_mem_nativeFlagStabilizer hg
  have h1 := peel1_mem_nativeFlagStabilizer h0
  have h2 := peel2_mem_nativeFlagStabilizer h1
  exact ⟨nativeFlagStabilizer_peel34_basis8_two_x2_coordinate_control h2,
    nativeFlagStabilizer_peel34_basis8_two_y1_coordinate_control h2⟩

theorem nativeFlagStabilizer_peel0_basis8_seven_x0_coordinate_control
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((peel0 g).1 (basis8 7)).x0 = false := by
  rw [peel0_apply_basis8_7]
  simp only [extractBit0]
  split
  · rw [automorphism_map_add, automorphism_map_add]
    change ((g.1 (basis8 2)).x0 ^^
      ((g.1 (basis8 6)).x0 ^^ (g.1 (basis8 7)).x0)) = false
    have h6 := nativeFlagStabilizer_basis8_six_coordinate_form hg
    have h6x0 : (g.1 (basis8 6)).x0 = false := by
      rw [h6]
    have h2 := nativeFlagStabilizer_basis8_two_x0 hg
    simp_all
  · exact Bool.eq_false_of_not_eq_true ‹¬ (g.1 (basis8 7)).x0 = true›

theorem nativeFlagStabilizer_peel1_basis8_seven_x0_invariant
    {f : SplitOctF2Aut}
    (hf : f ∈ nativeFlagStabilizer) :
    ((peel1 f).1 (basis8 7)).x0 = (f.1 (basis8 7)).x0 := by
  rw [peel1_basis8_7_readback]
  split
  · rw [automorphism_map_add, automorphism_map_add,
      automorphism_map_add, automorphism_map_add]
    have h4 := nativeFlagStabilizer_basis8_four hf
    have h6 := nativeFlagStabilizer_basis8_six_coordinate_form hf
    have hcart : add (f.1 ePlus) (f.1 eMinus) = one := by
      rw [← automorphism_map_add, ePlus_add_eMinus_eq_one, f.2.1]
    rw [← add_assoc, hcart, h4, h6]
    have hone_x0 : one.x0 = false := by rfl
    have hup2_x0 : up2.x0 = false := by rfl
    simp [add, add2, basis8, hone_x0, hup2_x0]
  · rfl

theorem mul_apply_basis8_fifth_x0_native (X : SplitOctF2) :
    (mul X (basis8 5)).x0 = false := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  simp [mul, dot3, cross0, cross1, cross2, basis8, down0,
    add2, mul2]

theorem nativeFlagStabilizer_basis8_three_x0_zero_of_fifth_fixed
    {g : SplitOctF2Aut}
    (h5 : g.1 (basis8 5) = basis8 5) :
    (g.1 (basis8 3)).x0 = false := by
  have hmul := nativeFlagStabilizer_basis8_seven_mul_fifth g
  rw [h5] at hmul
  have h0 := congrArg SplitOctF2.x0 hmul
  rw [mul_apply_basis8_fifth_x0_native] at h0
  exact h0.symm

theorem mul_apply_basis8_four_add_fifth_x0_native (X : SplitOctF2) :
    (mul X (add (basis8 4) (basis8 5))).x0 = false := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  simp [mul, dot3, cross0, cross1, cross2, basis8, up2, down0,
    add, add2, mul2]

theorem nativeFlagStabilizer_basis8_three_x0_zero
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (g.1 (basis8 3)).x0 = false := by
  rcases nativeFlagStabilizer_basis8_fifth_cases hg with h5 | h5
  · exact nativeFlagStabilizer_basis8_three_x0_zero_of_fifth_fixed h5
  · have hmul := nativeFlagStabilizer_basis8_seven_mul_fifth g
    rw [h5] at hmul
    have h0 := congrArg SplitOctF2.x0 hmul
    rw [mul_apply_basis8_four_add_fifth_x0_native] at h0
    exact h0.symm

theorem nativeFlagStabilizer_pc6pc3_basis8_seven_x0_false
    {f : SplitOctF2Aut}
    (hf : f ∈ nativeFlagStabilizer)
    (h7x0 : (f.1 (basis8 7)).x0 = false) :
    (f.1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 7))).x0 = false := by
  rw [automorphism_pc6pc3_basis8_seven_unit_reduced]
  have h3 := nativeFlagStabilizer_basis8_three_x0_zero hf
  have h6 := nativeFlagStabilizer_basis8_six_coordinate_form hf
  have h3' : (f.1 up1).x0 = false := by
    simpa [basis8, up1] using h3
  have h7' : (f.1 down2).x0 = false := by
    simpa [basis8, down2] using h7x0
  rw [h6] at *
  have hone : one.x0 = false := by rfl
  simp [add, add2, h3, h7x0, hone]

theorem nativeFlagStabilizer_peel2_basis8_seven_x0_readback
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((peel2 (peel1 (peel0 g))).1 (basis8 7)).x0 = false := by
  have h0 := peel0_mem_nativeFlagStabilizer hg
  have h1 := peel1_mem_nativeFlagStabilizer h0
  have h0x0 := nativeFlagStabilizer_peel0_basis8_seven_x0_coordinate_control hg
  have h1x0 := nativeFlagStabilizer_peel1_basis8_seven_x0_invariant h0
  have hfx0 : ((peel1 (peel0 g)).1 (basis8 7)).x0 = false := by
    rw [h1x0, h0x0]
  by_cases hx1 : ((peel1 (peel0 g)).1 (basis8 7)).x1 = true
  · rw [peel2_basis8_7_readback, hx1]
    exact nativeFlagStabilizer_pc6pc3_basis8_seven_x0_false h1 hfx0
  · have hx1' : ((peel1 (peel0 g)).1 (basis8 7)).x1 = false := by
      cases h : ((peel1 (peel0 g)).1 (basis8 7)).x1 <;> simp_all
    rw [peel2_basis8_7_readback, hx1']
    exact hfx0

theorem nativeFlagStabilizer_peel34_basis8_seven_x0_readback
    {f : SplitOctF2Aut}
    (hf : f ∈ nativeFlagStabilizer)
    (h7x0 : (f.1 (basis8 7)).x0 = false) :
    ((peel34 f).1 (basis8 7)).x0 = false := by
  have h4 := nativeFlagStabilizer_basis8_four hf
  have h6 := nativeFlagStabilizer_basis8_six_coordinate_form hf
  have hone : one.x0 = false := by rfl
  have h4x0 : (basis8 4).x0 = false := by rfl
  rw [peel34_basis8_7]
  dsimp
  split <;> split
  · rw [automorphism_map_ePlus_eMinus_basis8_4_basis8_7, h4]
    simp [add, add2, h7x0, hone, h4x0]
  · rw [automorphism_map_ePlus_eMinus_basis8_4_basis8_6_basis8_7, h4, h6]
    simp [add, add2, h7x0, hone, h4x0]
  · rw [automorphism_map_add, h6]
    simp [add, add2, h7x0, hone, h4x0]
  · exact h7x0

theorem nativeFlagStabilizer_peel34_basis8_seven_partial_shape
    {f : SplitOctF2Aut}
    (hf : f ∈ nativeFlagStabilizer)
    (h7x0 : (f.1 (basis8 7)).x0 = false) :
    ∃ a b x1 x2 y0 y1 y2 : F2Bit,
      (peel34 f).1 (basis8 7) =
        ⟨a, b, false, x1, x2, y0, y1, y2⟩ ∧
      a = b := by
  let h := (peel34 f).1 (basis8 7)
  have hx0 : h.x0 = false := by
    exact nativeFlagStabilizer_peel34_basis8_seven_x0_readback hf h7x0
  have h34 : peel34 f ∈ nativeFlagStabilizer :=
    peel34_mem_nativeFlagStabilizer hf
  have htrace : h.a = h.b :=
    nativeFlagStabilizer_basis8_seven_trace_zero h34
  refine ⟨h.a, h.b, h.x1, h.x2, h.y0, h.y1, h.y2, ?_, ?_⟩
  · change h = (⟨h.a, h.b, false, h.x1, h.x2, h.y0, h.y1, h.y2⟩ : SplitOctF2)
    rcases h with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
    change x0 = false at hx0
    subst x0
    rfl
  · exact htrace

theorem nativeFlagStabilizer_preceding_peel34_basis8_seven_partial_shape
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ∃ a b x1 x2 y0 y1 y2 : F2Bit,
      (peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 7) =
        ⟨a, b, false, x1, x2, y0, y1, y2⟩ ∧
      a = b := by
  have h0 := peel0_mem_nativeFlagStabilizer hg
  have h1 := peel1_mem_nativeFlagStabilizer h0
  have h2 := peel2_mem_nativeFlagStabilizer h1
  have h7x0 :
      ((peel2 (peel1 (peel0 g))).1 (basis8 7)).x0 = false :=
    nativeFlagStabilizer_peel2_basis8_seven_x0_readback hg
  exact nativeFlagStabilizer_peel34_basis8_seven_partial_shape h2 h7x0

theorem nativeFlagStabilizer_preceding_peel34_basis8_seven_partial_shape_with_y2
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ∃ a b x1 x2 y0 y1 : F2Bit,
      (peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 7) =
        ⟨a, b, false, x1, x2, y0, y1, true⟩ ∧
      a = b := by
  rcases nativeFlagStabilizer_preceding_peel34_basis8_seven_partial_shape hg with
    ⟨a, b, x1, x2, y0, y1, y2, hshape, hab⟩
  have hy2 :
      ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 7)).y2 = true :=
    nativeFlagStabilizer_peel34_basis8_seven_y2_readback hg
  refine ⟨a, b, x1, x2, y0, y1, ?_, hab⟩
  have hy2' := congrArg SplitOctF2.y2 hshape
  rw [hy2] at hy2'
  calc
    (peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 7) =
        ⟨a, b, false, x1, x2, y0, y1, y2⟩ := hshape
    _ = ⟨a, b, false, x1, x2, y0, y1, true⟩ := by rw [hy2']

theorem nativeFlagStabilizer_preceding_peel34_basis8_seven_x2_formula
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ∃ a x1 x2 y0 y1 : F2Bit,
      (peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 7) =
        ⟨a, a, false, x1, x2, y0, y1, true⟩ ∧
      x2 = Bool.xor a (x1 && y1) := by
  rcases nativeFlagStabilizer_preceding_peel34_basis8_seven_partial_shape_with_y2 hg with
    ⟨a, b, x1, x2, y0, y1, hshape, hab⟩
  have hsq :
      mul ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 7))
        ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 7)) = zero := by
    calc
      mul ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 7))
          ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 7)) =
          (peel34 (peel2 (peel1 (peel0 g)))).1
            (mul (basis8 7) (basis8 7)) :=
        ((peel34 (peel2 (peel1 (peel0 g)))).2.2.2
          (basis8 7) (basis8 7)).symm
      _ = (peel34 (peel2 (peel1 (peel0 g)))).1 zero := by rfl
      _ = zero :=
        InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.automorphism_map_zero
          (peel34 (peel2 (peel1 (peel0 g))))
  refine ⟨a, x1, x2, y0, y1, ?_, ?_⟩
  · rw [hshape, hab]
  · have hsq_a := congrArg SplitOctF2.a hsq
    have hzero : (zero : SplitOctF2).a = false := by rfl
    rw [hzero] at hsq_a
    rw [hshape, splitOct_basis8_seven_shape_square_a] at hsq_a
    cases a <;> cases x1 <;> cases y1 <;> cases x2 <;> simp_all

theorem nativeFlagStabilizer_preceding_peel34_basis8_seven_x0_readback
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 7)).x0 = false := by
  have h0 := peel0_mem_nativeFlagStabilizer hg
  have h1 := peel1_mem_nativeFlagStabilizer h0
  have h2 := peel2_mem_nativeFlagStabilizer h1
  have h7x0 :
      ((peel2 (peel1 (peel0 g))).1 (basis8 7)).x0 = false :=
    nativeFlagStabilizer_peel2_basis8_seven_x0_readback hg
  exact nativeFlagStabilizer_peel34_basis8_seven_x0_readback h2 h7x0

theorem nativeFlagStabilizer_preceding_peel34_basis8_seven_coordinate_certificate
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 7)).x0 = false) ∧
      (((peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 7)).y2 = true) := by
  constructor
  · exact nativeFlagStabilizer_preceding_peel34_basis8_seven_x0_readback hg
  · exact nativeFlagStabilizer_peel34_basis8_seven_y2_readback hg

theorem nativeFlagStabilizer_peel5_basis8_seven_x0_readback
    {f : SplitOctF2Aut}
    (hf : f ∈ nativeFlagStabilizer)
    (h7x0 : (f.1 (basis8 7)).x0 = false) :
    ((peel5 f).1 (basis8 7)).x0 = false := by
  rw [peel5_basis8_7_readback]
  split
  · rw [active_basis8_seven_vector_eq_basis8_fifth_add_seventh]
    rw [automorphism_map_add]
    have h5x0 : (f.1 (basis8 5)).x0 = false := by
      rcases nativeFlagStabilizer_basis8_fifth_cases hf with h5 | h5
      · rw [h5]
        rfl
      · rw [h5]
        rfl
    simp [add, add2, h5x0, h7x0]
  · exact h7x0

theorem nativeFlagStabilizer_fullPeel_basis8_seven_x0_readback_via_peeling
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 7)).x0 = false := by
  let f := peel34 (peel2 (peel1 (peel0 g)))
  have hf : f ∈ nativeFlagStabilizer := by
    dsimp [f]
    exact peel34_mem_nativeFlagStabilizer
      (peel2_mem_nativeFlagStabilizer
        (peel1_mem_nativeFlagStabilizer
          (peel0_mem_nativeFlagStabilizer hg)))
  have hfx0 : (f.1 (basis8 7)).x0 = false := by
    exact nativeFlagStabilizer_preceding_peel34_basis8_seven_x0_readback hg
  have h5x0 := nativeFlagStabilizer_peel5_basis8_seven_x0_readback hf hfx0
  simpa [fullPeel, f] using h5x0

theorem nativeFlagStabilizer_fullPeel_basis8_seven_coordinate_certificate
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (((fullPeel g).1 (basis8 7)).x0 = false) ∧
      (((fullPeel g).1 (basis8 7)).y2 = true) := by
  constructor
  · exact nativeFlagStabilizer_fullPeel_basis8_seven_x0_readback_via_peeling hg
  · exact fullPeel_basis8_seven_y2_of_stabilizer hg

theorem peel2_basis8_seven_fixed_of_x1_false
    {f : SplitOctF2Aut}
    (hx1 : (f.1 (basis8 7)).x1 = false) :
    (peel2 f).1 (basis8 7) = f.1 (basis8 7) := by
  rw [peel2_basis8_7_readback, hx1]
  rfl

/-! The two branches of `peel2_basis8_7_readback` packaged as one local
assembly lemma.  The transformed branch is an explicit native readback
hypothesis; it is not inferred from subgroup generation or cardinality. -/
theorem peel2_basis8_seven_fixed_of_branch_readback
    {f : SplitOctF2Aut}
    (hbranch :
      ((f.1 (basis8 7)).x1 = false ∧
        f.1 (basis8 7) = basis8 7) ∨
      ((f.1 (basis8 7)).x1 = true ∧
        f.1 (add ePlus (add eMinus (add (basis8 3)
          (add (basis8 6) (basis8 7))))) = basis8 7)) :
    (peel2 f).1 (basis8 7) = basis8 7 := by
  rcases hbranch with hbranch | hbranch
  · exact (peel2_basis8_seven_fixed_of_x1_false hbranch.1).trans hbranch.2
  · rw [peel2_basis8_7_readback, hbranch.1, hbranch.2]
    rfl

theorem peel2_basis8_seven_y2_projection
    (f : SplitOctF2Aut) :
    ((peel2 f).1 (basis8 7)).y2 =
      if (f.1 (basis8 7)).x1 then
        (f.1 (add ePlus (add eMinus (add (basis8 3)
          (add (basis8 6) (basis8 7)))))).y2
      else (f.1 (basis8 7)).y2 := by
  rw [peel2_basis8_7_readback]
  split <;> rfl

theorem nativeFlagStabilizer_peel0_basis8_seven_y2_readback
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    ((peel0 g).1 (basis8 7)).y2 = (g.1 (basis8 7)).y2 := by
  have h2 := nativeFlagStabilizer_basis8_two_y2 hg
  have h6 := nativeFlagStabilizer_basis8_six_coordinate_form hg
  have h6y2 : (g.1 (basis8 6)).y2 = false := by
    have := congrArg SplitOctF2.y2 h6
    simp [h6] at this ⊢
  rw [peel0_apply_basis8_7]
  split
  · rw [automorphism_map_add, automorphism_map_add]
    change ((g.1 (basis8 2)).y2 ^^
      ((g.1 (basis8 6)).y2 ^^ (g.1 (basis8 7)).y2)) =
      (g.1 (basis8 7)).y2
    simp [h2, h6y2]
  · rfl

theorem nativeFlagStabilizer_peel1_basis8_seven_y2_readback
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    ((peel1 g).1 (basis8 7)).y2 = (g.1 (basis8 7)).y2 := by
  have h4 := nativeFlagStabilizer_basis8_four hg
  have h6 := nativeFlagStabilizer_basis8_six_coordinate_form hg
  have h6y2 : (g.1 (basis8 6)).y2 = false := by
    have := congrArg SplitOctF2.y2 h6
    simp [h6] at this ⊢
  have h7y2 := nativeFlagStabilizer_basis8_seven_y2 hg
  have hcart : ((g.1 ePlus).y2 ^^ (g.1 eMinus).y2) = false := by
    have hone : g.1 (add ePlus eMinus) = g.1 one := by
      rw [ePlus_add_eMinus_eq_one]
    have hmap := congrArg SplitOctF2.y2 hone
    rw [automorphism_map_add, g.2.1] at hmap
    change ((g.1 ePlus).y2 ^^ (g.1 eMinus).y2) = false at hmap
    exact hmap
  rw [peel1_basis8_7_readback]
  split
  · rw [automorphism_map_add, automorphism_map_add,
      automorphism_map_add, automorphism_map_add]
    simp [add, add2, h4, h6y2, h7y2]
    cases he : (g.1 ePlus).y2 <;>
      cases hm : (g.1 eMinus).y2 <;>
      simp_all <;> rfl
  · rfl

theorem nativeFlagStabilizer_peel34_y1_x2_control
    {g : SplitOctF2Aut}
    (_hg : g ∈ nativeFlagStabilizer) :
    let f := peel2 (peel1 (peel0 g))
    (((peel34 f).1 (basis8 2)).y1 =
        if (f.1 (basis8 2)).y1 then
          (f.1 (add (basis8 2) (basis8 6))).y1
        else (f.1 (basis8 2)).y1) ∧
      ((peel34 f).1 (basis8 2)).x2 =
        if (f.1 (basis8 2)).y1 then
          (f.1 (add (basis8 2) (basis8 6))).x2
        else (f.1 (basis8 2)).x2 := by
  dsimp
  constructor
  · exact peel34_basis8_2_y1 (peel2 (peel1 (peel0 g)))
  · exact peel34_basis8_2_x2 (peel2 (peel1 (peel0 g)))

theorem automorphism_basis8_two_add_six_y1
    (g : SplitOctF2Aut) :
    (g.1 (add (basis8 2) (basis8 6))).y1 =
      (add (g.1 (basis8 2)) (g.1 (basis8 6))).y1 := by
  rw [g.2.2.1]

theorem automorphism_basis8_two_add_six_x2
    (g : SplitOctF2Aut) :
    (g.1 (add (basis8 2) (basis8 6))).x2 =
      (add (g.1 (basis8 2)) (g.1 (basis8 6))).x2 := by
  rw [g.2.2.1]

theorem mul_basis8_two_two : mul (basis8 2) (basis8 2) = zero := rfl

theorem fullPeel_basis8_two_square_zero
    {g : SplitOctF2Aut} :
    mul ((fullPeel g).1 (basis8 2)) ((fullPeel g).1 (basis8 2)) = zero := by
  calc
    mul ((fullPeel g).1 (basis8 2)) ((fullPeel g).1 (basis8 2)) =
        (fullPeel g).1 (mul (basis8 2) (basis8 2)) :=
      ((fullPeel g).2.2.2 (basis8 2) (basis8 2)).symm
    _ = (fullPeel g).1 zero := by rw [mul_basis8_two_two]
    _ = zero :=
      InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge.automorphism_map_zero
        (fullPeel g)

theorem peel0_basis8_zero_branch_formula (f : SplitOctF2Aut) :
    (peel0 f).1 (basis8 0) =
      if (f.1 (basis8 7)).x0 then
        f.1 (pc1Fun (basis8 0))
      else f.1 (basis8 0) := by
  dsimp [peel0]
  split
  · rw [automorphism_mul_apply]
    rfl
  · rfl

theorem peel1_basis8_zero_branch_formula (f : SplitOctF2Aut) :
    (peel1 f).1 (basis8 0) =
      if (f.1 (basis8 2)).x1 then
        f.1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
          G2TwoSylowPCAutomorphisms.pc2Aut).1 (basis8 0))
      else f.1 (basis8 0) := by
  dsimp [peel1]
  split
  · rw [automorphism_mul_apply]
  · rfl

theorem splitOct_eq_basis8_two_of_coordinate_readback
    (X : SplitOctF2)
    (ha : X.a = false) (hb : X.b = false)
    (hx0 : X.x0 = true) (hx1 : X.x1 = false)
    (hx2 : X.x2 = false) (hy0 : X.y0 = false)
    (hy1 : X.y1 = false) (hy2 : X.y2 = false) :
    X = basis8 2 := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  change a = false at ha
  change b = false at hb
  change x0 = true at hx0
  change x1 = false at hx1
  change x2 = false at hx2
  change y0 = false at hy0
  change y1 = false at hy1
  change y2 = false at hy2
  subst a
  subst b
  subst x0
  subst x1
  subst x2
  subst y0
  subst y1
  subst y2
  rfl

theorem fullPeel_basis8_two_x0_eq_basis8_zero_a
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 2)).x0 =
      ((fullPeel g).1 (basis8 0)).a := by
  exact nativeFlagStabilizer_basis8_two_x0_eq_basis8_zero_a
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)

theorem fullPeel_basis8_zero_a
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 0)).a = true := by
  exact nativeFlagStabilizer_basis8_zero_a
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)

theorem fullPeel_basis8_two_x0
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 2)).x0 = true := by
  exact nativeFlagStabilizer_basis8_two_x0
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)

theorem fullPeel_basis8_two_y2
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 2)).y2 = false := by
  exact nativeFlagStabilizer_basis8_two_y2
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)

theorem fullPeel_basis8_two_partial_shape
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    ∃ a b x1 x2 y0 y1 : F2Bit,
      (fullPeel g).1 (basis8 2) = ⟨a, b, true, x1, x2, y0, y1, false⟩ := by
  let X := (fullPeel g).1 (basis8 2)
  have hx0 : X.x0 = true := fullPeel_basis8_two_x0 hg
  have hy2 : X.y2 = false := fullPeel_basis8_two_y2 hg
  refine ⟨X.a, X.b, X.x1, X.x2, X.y0, X.y1, ?_⟩
  change X = ⟨X.a, X.b, true, X.x1, X.x2, X.y0, X.y1, false⟩
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  change x0 = true at hx0
  change y2 = false at hy2
  subst x0
  subst y2
  rfl

theorem fullPeel_basis8_two_trace_zero_shape
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    ∃ a x1 x2 y0 y1 : F2Bit,
      (fullPeel g).1 (basis8 2) =
        ⟨a, a, true, x1, x2, y0, y1, false⟩ := by
  let X := (fullPeel g).1 (basis8 2)
  have hshape := fullPeel_basis8_two_partial_shape hg
  have htrace := nativeFlagStabilizer_basis8_two_trace_zero
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)
  rcases hshape with ⟨a, b, x1, x2, y0, y1, hX⟩
  refine ⟨a, x1, x2, y0, y1, ?_⟩
  rw [hX]
  rw [hX] at htrace
  cases htrace
  rfl

theorem mul_basis8_two_basis8_fifth_a (X : SplitOctF2) :
    (mul X (basis8 5)).a = X.x0 := by
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  simp [mul, dot3, cross0, cross1, cross2, basis8, up0, up1, up2,
    down0, down1, down2, ePlus, eMinus, add2, mul2]

theorem mul_basis8_two_add_four_fifth_a (X : SplitOctF2) :
    (mul X (add (basis8 4) (basis8 5))).a = X.x0 := by
  rw [mul_add]
  rcases X with ⟨a, b, x0, x1, x2, y0, y1, y2⟩
  simp [mul, dot3, cross0, cross1, cross2, basis8, up0, up1, up2,
    down0, down1, down2, ePlus, eMinus, add2, mul2]
  simp [add, add2]

theorem fullPeel_basis8_two_readback_of_preceding
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (h2 : (peel34 (peel2 (peel1 (peel0 g)))).1 (basis8 2) = basis8 2) :
    (fullPeel g).1 (basis8 2) = basis8 2 := by
  exact fullPeel_basis8_two_fixed_of_preceding_readbacks
    h2 (preceding_peel34_basis8_four_readback hg)

theorem fullPeel_basis8_two_readback_of_stabilizer_of_fixed
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (h2 : g.1 (basis8 2) = basis8 2)
    (h7 : ((peel1 (peel0 g)).1 (basis8 7)).x1 = false) :
    (fullPeel g).1 (basis8 2) = basis8 2 := by
  exact fullPeel_basis8_two_readback_of_preceding hg
    (preceding_peel34_basis8_two_readback h2 h7)

theorem automorphism_basis8_all_fixed_of_generators_fixed
    (f : SplitOctF2Aut)
    (h2 : f.1 (basis8 2) = basis8 2)
    (h4 : f.1 (basis8 4) = basis8 4)
    (h5 : f.1 (basis8 5) = basis8 5)
    (h7 : f.1 (basis8 7) = basis8 7) :
    ∀ j : Fin 8, f.1 (basis8 j) = basis8 j := by
  intro j
  fin_cases j
  · change f.1 (basis8 0) = basis8 0
    have he : basis8 0 = mul (basis8 2) (basis8 5) := rfl
    rw [he, f.2.2.2, h2, h5]
  · change f.1 (basis8 1) = basis8 1
    have he : basis8 1 = mul (basis8 5) (basis8 2) := rfl
    rw [he, f.2.2.2, h5, h2]
  · exact h2
  · change f.1 (basis8 3) = basis8 3
    have he : basis8 3 = mul (basis8 7) (basis8 5) := rfl
    rw [he, f.2.2.2, h7, h5]
  · exact h4
  · exact h5
  · change f.1 (basis8 6) = basis8 6
    have he : basis8 6 = mul (basis8 4) (basis8 2) := rfl
    rw [he, f.2.2.2, h4, h2]
  · exact h7

theorem fullPeel_mem_unipotent_of_four_generators_fixed
    {g : SplitOctF2Aut}
    (h2 : (fullPeel g).1 (basis8 2) = basis8 2)
    (h4 : (fullPeel g).1 (basis8 4) = basis8 4)
    (h5 : (fullPeel g).1 (basis8 5) = basis8 5)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7) :
    fullPeel g ∈ unipotentSubgroup := by
  apply fullPeel_mem_unipotent_of_basis_readback
  exact automorphism_basis8_all_fixed_of_generators_fixed (fullPeel g) h2 h4 h5 h7

theorem fullPeel_basis8_two_residual_shape
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    ∃ a x1 y0 y1 : F2Bit,
      (fullPeel g).1 (basis8 2) =
        ⟨a, a, true, x1, false, y0, y1, false⟩ := by
  rcases fullPeel_basis8_two_trace_zero_shape hg with
    ⟨a, x1, x2, y0, y1, hshape⟩
  have hx2 := fullPeel_basis8_two_x2 hg
  rw [hshape] at hx2
  change x2 = false at hx2
  subst x2
  exact ⟨a, x1, y0, y1, hshape⟩

theorem fullPeel_basis8_two_residual_peirce_relation
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    add2 ((fullPeel g).1 (basis8 2)).y0
      (mul2 ((fullPeel g).1 (basis8 2)).x1
        ((fullPeel g).1 (basis8 2)).y1) =
      ((fullPeel g).1 (basis8 2)).a := by
  exact nativeFlagStabilizer_basis8_two_peirce_dot3_formula
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)

theorem fullPeel_basis8_two_residual_coordinate_certificate
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    ∃ a x1 y0 y1 : F2Bit,
      (fullPeel g).1 (basis8 2) =
        ⟨a, a, true, x1, false, y0, y1, false⟩ ∧
      add2 y0 (mul2 x1 y1) = a := by
  rcases fullPeel_basis8_two_residual_shape hg with
    ⟨a, x1, y0, y1, hshape⟩
  refine ⟨a, x1, y0, y1, hshape, ?_⟩
  have hrel := fullPeel_basis8_two_residual_peirce_relation hg
  rw [hshape] at hrel
  exact hrel

theorem mul_apply_basis8_three_b (X : SplitOctF2) :
    (mul X (basis8 3)).b = X.y1 := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  simp [mul, dot3, basis8, up1, add2, mul2]

theorem mul_apply_basis8_three_x1 (X : SplitOctF2) :
    (mul X (basis8 3)).x1 = X.a := by
  rcases X with ⟨a,b,x0,x1,x2,y0,y1,y2⟩
  simp [mul, cross1, basis8, up1, add2, mul2]

theorem peel1_basis8_six_y0
    (f : SplitOctF2Aut) :
    ((peel1 f).1 (basis8 6)).y0 =
      if (f.1 (basis8 2)).x1 then
        (f.1 (add (basis8 5) (basis8 6))).y0
      else (f.1 (basis8 6)).y0 := by
  dsimp [peel1]
  split
  · rw [automorphism_mul_apply, pc6pc2_basis8_6]
  · rfl

theorem pc6pc3_basis8_6_y0 :
    ((G2TwoSylowPCAutomorphisms.pc6Aut *
      G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 6)).y0 = false := by
  change (G2TwoSylowPCGenerators.pc3Fun
    (G2TwoSylowPCGenerators.pc6Fun (basis8 6))).y0 = false
  simp [G2TwoSylowPCGenerators.pc3Fun,
    G2TwoSylowPCGenerators.pc6Fun, basis8, ePlus, eMinus,
    up0, up1, up2, down0, down1, down2]

theorem peel2_basis8_six_y0
    (f : SplitOctF2Aut) :
    ((peel2 f).1 (basis8 6)).y0 =
      if (f.1 (basis8 7)).x1 then
        (f.1 ((G2TwoSylowPCAutomorphisms.pc6Aut *
          G2TwoSylowPCAutomorphisms.pc3Aut).1 (basis8 6))).y0
      else (f.1 (basis8 6)).y0 := by
  dsimp [peel2]
  split
  · rw [automorphism_mul_apply]
  · rfl

theorem fullPeel_basis8_three_readback_of_generators
    {g : SplitOctF2Aut}
    (h5 : (fullPeel g).1 (basis8 5) = basis8 5)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7) :
    (fullPeel g).1 (basis8 3) = basis8 3 := by
  have he : basis8 3 = mul (basis8 7) (basis8 5) := rfl
  calc
    (fullPeel g).1 (basis8 3) = (fullPeel g).1 (mul (basis8 7) (basis8 5)) := by rw [he]
    _ = mul ((fullPeel g).1 (basis8 7)) ((fullPeel g).1 (basis8 5)) :=
      (fullPeel g).2.2.2 (basis8 7) (basis8 5)
    _ = mul (basis8 7) (basis8 5) := by rw [h7, h5]
    _ = basis8 3 := rfl

theorem fullPeel_basis8_two_mul_three_of_generators
    {g : SplitOctF2Aut}
    (h3 : (fullPeel g).1 (basis8 3) = basis8 3)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7) :
    mul ((fullPeel g).1 (basis8 2)) (basis8 3) = basis8 7 := by
  have he : basis8 7 = mul (basis8 2) (basis8 3) := rfl
  calc
    mul ((fullPeel g).1 (basis8 2)) (basis8 3) =
        mul ((fullPeel g).1 (basis8 2)) ((fullPeel g).1 (basis8 3)) := by rw [h3]
    _ = (fullPeel g).1 (mul (basis8 2) (basis8 3)) :=
      ((fullPeel g).2.2.2 (basis8 2) (basis8 3)).symm
    _ = (fullPeel g).1 (basis8 7) := by rw [he]
    _ = basis8 7 := h7

theorem fullPeel_basis8_two_y1_of_generators
    {g : SplitOctF2Aut}
    (h3 : (fullPeel g).1 (basis8 3) = basis8 3)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7) :
    ((fullPeel g).1 (basis8 2)).y1 = false := by
  have hmul := fullPeel_basis8_two_mul_three_of_generators h3 h7
  have hb : (mul ((fullPeel g).1 (basis8 2)) (basis8 3)).b = (basis8 7 : SplitOctF2).b := by
    rw [hmul]
  have hproj := mul_apply_basis8_three_b ((fullPeel g).1 (basis8 2))
  have h7b : (basis8 7 : SplitOctF2).b = false := rfl
  rw [hproj] at hb
  rw [h7b] at hb
  exact hb

theorem fullPeel_basis8_two_a_of_generators
    {g : SplitOctF2Aut}
    (h3 : (fullPeel g).1 (basis8 3) = basis8 3)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7) :
    ((fullPeel g).1 (basis8 2)).a = false := by
  have hmul := fullPeel_basis8_two_mul_three_of_generators h3 h7
  have hx1 : (mul ((fullPeel g).1 (basis8 2)) (basis8 3)).x1 = (basis8 7 : SplitOctF2).x1 := by
    rw [hmul]
  have hproj := mul_apply_basis8_three_x1 ((fullPeel g).1 (basis8 2))
  have h7x1 : (basis8 7 : SplitOctF2).x1 = false := rfl
  rw [hproj] at hx1
  rw [h7x1] at hx1
  exact hx1

theorem fullPeel_basis8_two_b_of_generators
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer)
    (h3 : (fullPeel g).1 (basis8 3) = basis8 3)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7) :
    ((fullPeel g).1 (basis8 2)).b = false := by
  have htr := nativeFlagStabilizer_basis8_two_trace_zero
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)
  have ha := fullPeel_basis8_two_a_of_generators h3 h7
  rw [← htr]
  exact ha

theorem fullPeel_basis8_two_y0_of_generators
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer)
    (h3 : (fullPeel g).1 (basis8 3) = basis8 3)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7) :
    ((fullPeel g).1 (basis8 2)).y0 = false := by
  have hrel := fullPeel_basis8_two_residual_peirce_relation hg
  have ha := fullPeel_basis8_two_a_of_generators h3 h7
  have hy1 := fullPeel_basis8_two_y1_of_generators h3 h7
  rw [ha, hy1] at hrel
  simpa [add2, mul2] using hrel

theorem fullPeel_basis8_two_residual_reduced_shape
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer)
    (h3 : (fullPeel g).1 (basis8 3) = basis8 3)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7) :
    ∃ x1 : F2Bit,
      (fullPeel g).1 (basis8 2) =
        ⟨false, false, true, x1, false, false, false, false⟩ := by
  rcases fullPeel_basis8_two_residual_shape hg with
    ⟨a, x1, y0, y1, hshape⟩
  have ha := fullPeel_basis8_two_a_of_generators h3 h7
  have hy1 := fullPeel_basis8_two_y1_of_generators h3 h7
  have hy0 := fullPeel_basis8_two_y0_of_generators hg h3 h7
  rw [hshape] at ha hy1 hy0
  change a = false at ha
  change y1 = false at hy1
  change y0 = false at hy0
  subst a
  subst y1
  subst y0
  exact ⟨x1, hshape⟩

theorem fullPeel_basis8_two_readback_of_reduced_shape
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer)
    (h3 : (fullPeel g).1 (basis8 3) = basis8 3)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7)
    (hx1 : ((fullPeel g).1 (basis8 2)).x1 = false) :
    (fullPeel g).1 (basis8 2) = basis8 2 := by
  rcases fullPeel_basis8_two_residual_reduced_shape hg h3 h7 with
    ⟨x1, hshape⟩
  rw [hshape] at hx1
  change x1 = false at hx1
  subst x1
  simpa [basis8] using hshape

theorem fullPeel_mem_unipotent_of_generators_and_x1
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer)
    (h3 : (fullPeel g).1 (basis8 3) = basis8 3)
    (h4 : (fullPeel g).1 (basis8 4) = basis8 4)
    (h5 : (fullPeel g).1 (basis8 5) = basis8 5)
    (h7 : (fullPeel g).1 (basis8 7) = basis8 7)
    (hx1 : ((fullPeel g).1 (basis8 2)).x1 = false) :
    fullPeel g ∈ unipotentSubgroup := by
  have h2 := fullPeel_basis8_two_readback_of_reduced_shape hg h3 h7 hx1
  exact fullPeel_mem_unipotent_of_four_generators_fixed h2 h4 h5 h7

theorem fullPeel_basis8_two_x1_eq_basis8_six_y0
    {g : SplitOctF2Aut} (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 2)).x1 =
      ((fullPeel g).1 (basis8 6)).y0 := by
  have hform := nativeFlagStabilizer_basis8_six_coordinate_form
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)
  have hy0 := congrArg SplitOctF2.y0 hform
  exact hy0.symm

theorem fullPeel_unipotent_eq_one
    {u : SplitOctF2Aut} (hu : u ∈ unipotentSubgroup) :
    fullPeel u = 1 := by
  rcases hu with ⟨e, rfl⟩
  exact fullPeel_pcWord_eq_one e

theorem fullPeel_basis8_seven_readback_of_mem_unipotent
    {u : SplitOctF2Aut} (hu : u ∈ unipotentSubgroup) :
    (fullPeel u).1 (basis8 7) = basis8 7 := by
  rw [fullPeel_unipotent_eq_one hu]
  rfl

/-! The residual remains a native flag-stabilizer element.  Consequently the
    stabilizer's exact `basis8 7` coordinate invariant transports to the
    residual without assuming that the residual is already unipotent. -/
theorem fullPeel_basis8_seven_y2
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 7)).y2 = true := by
  exact nativeFlagStabilizer_basis8_seven_y2
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)

theorem fullPeel_basis8_seven_trace_zero
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 7)).a =
      ((fullPeel g).1 (basis8 7)).b := by
  exact nativeFlagStabilizer_basis8_seven_trace_zero
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)

theorem fullPeel_basis8_seven_x0_eq_basis8_fifth_x2
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 7)).x0 =
      ((fullPeel g).1 (basis8 5)).x2 := by
  exact nativeFlagStabilizer_basis8_seven_x0_eq_basis8_fifth_x2
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)

theorem fullPeel_basis8_seven_x0_fifth_cases
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    (((fullPeel g).1 (basis8 7)).x0 = false ∧
        (fullPeel g).1 (basis8 5) = basis8 5) ∨
      (((fullPeel g).1 (basis8 7)).x0 = true ∧
        (fullPeel g).1 (basis8 5) = add (basis8 4) (basis8 5)) := by
  exact nativeFlagStabilizer_basis8_seven_x0_iff_fifth_cases
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)

theorem fullPeel_basis8_seven_residual_certificate
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ((fullPeel g).1 (basis8 7)).y2 = true ∧
      ((fullPeel g).1 (basis8 7)).a =
        ((fullPeel g).1 (basis8 7)).b ∧
      ((((fullPeel g).1 (basis8 7)).x0 = false ∧
          (fullPeel g).1 (basis8 5) = basis8 5) ∨
        (((fullPeel g).1 (basis8 7)).x0 = true ∧
          (fullPeel g).1 (basis8 5) =
            add (basis8 4) (basis8 5))) := by
  exact ⟨fullPeel_basis8_seven_y2 hg,
    fullPeel_basis8_seven_trace_zero hg,
    fullPeel_basis8_seven_x0_fifth_cases hg⟩

theorem fullPeel_basis8_seven_readback_of_mem_directGeneratorClosure
    {u : SplitOctF2Aut}
    (hu : u ∈ Subgroup.closure directFlagPCGenerators) :
    (fullPeel u).1 (basis8 7) = basis8 7 := by
  apply fullPeel_basis8_seven_readback_of_mem_unipotent
  rw [← directFlagPCGenerators_closure_eq_unipotentSubgroup]
  exact hu

end InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback

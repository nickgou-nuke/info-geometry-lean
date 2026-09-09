import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback
import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport
import InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
import InfoGeometry.Algebra.Zorn.G2PCRecoveryFactorization
import InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier

/-!
# Faithful matrix readback for the native flag stabilizer

This owner isolates the exact bridge needed for the reverse stabilizer
inclusion.  Once a stabilizer element is identified with a `pcMatrix`, the
existing faithful matrix representation and PC recovery immediately give
membership in the native unipotent subgroup.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerReadback
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2PCRecoveryFactorization
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup

theorem mem_unipotentSubgroup_of_matrix_readback
    {g : SplitOctF2Aut} {e : PCExponent}
    (hmat : autMatrix g = pcMatrix e) :
    g ∈ unipotentSubgroup := by
  change g ∈ Set.range G2TwoSylowSubgroup.pcWord
  refine ⟨e, ?_⟩
  apply autMatrix_injective
  simpa [pcMatrix] using hmat.symm

theorem mem_unipotentSubgroup_of_basis_action_eq
    {g : SplitOctF2Aut} {e : PCExponent}
    (h_basis : ∀ j : Fin 8,
      g.1 (basis8 j) =
        (G2TwoSylowSubgroup.pcWord e).1 (basis8 j)) :
    g ∈ unipotentSubgroup := by
  apply mem_unipotentSubgroup_of_matrix_readback
  ext i j
  rw [autMatrix_entry, pcMatrix]
  exact congrArg (fun X : SplitOctF2 => carrierToVec X i) (h_basis j)

theorem mem_unipotentSubgroup_of_fullPeel_eq_one
    {g : SplitOctF2Aut}
    (hpeel : fullPeel g = 1) :
    g ∈ unipotentSubgroup := by
  have hfactor := fullPeel_pcWord_factorization g
  have hfactor' : G2TwoSylowSubgroup.pcWord (extractAllBits g) = g := by
    simpa [hpeel] using hfactor
  rw [← hfactor']
  change G2TwoSylowSubgroup.pcWord (extractAllBits g) ∈
    Set.range G2TwoSylowSubgroup.pcWord
  exact ⟨G2TwoPCRecovery.extractAllBits g, rfl⟩

theorem fullPeel_mem_nativeFlagStabilizer_of_mem
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    fullPeel g ∈ nativeFlagStabilizer := by
  have hpc : G2TwoSylowSubgroup.pcWord (extractAllBits g) ∈
      unipotentSubgroup := by
    change G2TwoSylowSubgroup.pcWord (extractAllBits g) ∈
      Set.range G2TwoSylowSubgroup.pcWord
    exact ⟨extractAllBits g, rfl⟩
  have hpc' : G2TwoSylowSubgroup.pcWord (extractAllBits g) ∈
      nativeFlagStabilizer :=
    unipotentSubgroup_le_nativeFlagStabilizer hpc
  have hres := nativeFlagStabilizer.mul_mem
    (nativeFlagStabilizer.inv_mem hpc') hg
  have hfactor := fullPeel_pcWord_factorization g
  have heq :
      (G2TwoSylowSubgroup.pcWord (extractAllBits g))⁻¹ * g =
        fullPeel g := by
    calc
      (G2TwoSylowSubgroup.pcWord (extractAllBits g))⁻¹ * g =
          (G2TwoSylowSubgroup.pcWord (extractAllBits g))⁻¹ *
            (G2TwoSylowSubgroup.pcWord (extractAllBits g) * fullPeel g) := by
              rw [hfactor]
      _ = fullPeel g := by group
  simpa [heq] using hres

/-! A stabilizer element therefore has a canonical recovered-PC factor and a
residual factor which is still constrained by the same flag.  This is the
precise decomposition needed by the reverse-inclusion proof; no claim that
the residual factor is already trivial is made here. -/
theorem nativeFlagStabilizer_pcWord_residual_decomposition
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    ∃ e : PCExponent,
      g = G2TwoSylowSubgroup.pcWord e * fullPeel g ∧
        fullPeel g ∈ nativeFlagStabilizer := by
  refine ⟨extractAllBits g, ?_, ?_⟩
  · exact (fullPeel_pcWord_factorization g).symm
  · exact fullPeel_mem_nativeFlagStabilizer_of_mem hg

theorem fullPeel_mem_nativePointStabilizer_of_nativeFlagStabilizer
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer) :
    fullPeel g ∈ G2NativeOnePointStabilizer.nativePointStabilizer := by
  exact nativeFlagStabilizer_le_nativePointStabilizer
    (fullPeel_mem_nativeFlagStabilizer_of_mem hg)

theorem mem_unipotent_iff_fullPeel_mem_unipotent
    {g : SplitOctF2Aut} :
    g ∈ unipotentSubgroup ↔ fullPeel g ∈ unipotentSubgroup := by
  have hfactor := fullPeel_pcWord_factorization g
  have hpc : G2TwoSylowSubgroup.pcWord (extractAllBits g) ∈
      unipotentSubgroup := by
    change G2TwoSylowSubgroup.pcWord (extractAllBits g) ∈
      Set.range G2TwoSylowSubgroup.pcWord
    exact ⟨extractAllBits g, rfl⟩
  constructor
  · intro hgU
    have hres := unipotentSubgroup.mul_mem
      (unipotentSubgroup.inv_mem hpc) hgU
    have heq :
        (G2TwoSylowSubgroup.pcWord (extractAllBits g))⁻¹ * g =
          fullPeel g := by
      calc
        (G2TwoSylowSubgroup.pcWord (extractAllBits g))⁻¹ * g =
            (G2TwoSylowSubgroup.pcWord (extractAllBits g))⁻¹ *
              (G2TwoSylowSubgroup.pcWord (extractAllBits g) * fullPeel g) := by
                rw [hfactor]
        _ = fullPeel g := by group
    simpa [heq] using hres
  · intro hres
    have hgU := unipotentSubgroup.mul_mem hpc hres
    simpa [hfactor] using hgU

theorem nativeFlagStabilizer_le_unipotent_of_fullPeel_eq_one
    (hpeel : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      fullPeel g = 1) :
    nativeFlagStabilizer ≤ unipotentSubgroup := by
  intro g hg
  exact mem_unipotentSubgroup_of_fullPeel_eq_one (hpeel g hg)

theorem nativeFlagStabilizer_le_unipotent_of_fullPeel_mem
    (hres : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      fullPeel g ∈ unipotentSubgroup) :
    nativeFlagStabilizer ≤ unipotentSubgroup := by
  intro g hg
  exact (mem_unipotent_iff_fullPeel_mem_unipotent).mpr (hres g hg)

theorem nativeFlagStabilizer_le_unipotent_of_matrix_readback
    (hreadback : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      ∃ e : PCExponent, autMatrix g = pcMatrix e) :
    nativeFlagStabilizer ≤ unipotentSubgroup := by
  intro g hg
  obtain ⟨e, hmat⟩ := hreadback g hg
  exact mem_unipotentSubgroup_of_matrix_readback hmat

theorem nativeFlagStabilizer_eq_unipotent_of_matrix_readback
    (hreadback : ∀ g : SplitOctF2Aut, g ∈ nativeFlagStabilizer →
      ∃ e : PCExponent, autMatrix g = pcMatrix e) :
    nativeFlagStabilizer = unipotentSubgroup := by
  apply le_antisymm
  · exact nativeFlagStabilizer_le_unipotent_of_matrix_readback hreadback
  · exact unipotentSubgroup_le_nativeFlagStabilizer

end InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback

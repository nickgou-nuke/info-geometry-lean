import InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Native containment of the direct flag-generator closure

The direct generator set is a native PC-word datum.  This file records the
containment which follows from the already proved subgroup containments; it
does not assert that these generators generate the whole stabilizer.
-/

namespace InfoGeometry.Algebra.Zorn.G2NativeFlagGeneratorClosureBridge

open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerTransport
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2NativeFlagMatrixReadback
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2PCRecoveryFactorization
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

theorem directFlagPCGenerators_closure_le_nativeFlagStabilizer :
    Subgroup.closure directFlagPCGenerators ≤ nativeFlagStabilizer := by
  refine (Subgroup.closure_le _).2 ?_
  intro g hg
  exact unipotentSubgroup_le_nativeFlagStabilizer
    (directFlagPCGenerators_subset_unipotentSubgroup hg)

theorem directFlagPCGenerators_closure_le_both :
    Subgroup.closure directFlagPCGenerators ≤ unipotentSubgroup ∧
      Subgroup.closure directFlagPCGenerators ≤ nativeFlagStabilizer := by
  exact ⟨directFlagPCGenerators_closure_le_unipotentSubgroup,
    directFlagPCGenerators_closure_le_nativeFlagStabilizer⟩

theorem directFlagPCGenerators_closure_eq_unipotentSubgroup :
    Subgroup.closure directFlagPCGenerators = unipotentSubgroup := by
  apply le_antisymm
  · exact directFlagPCGenerators_closure_le_unipotentSubgroup
  · exact unipotentSubgroup_le_directFlagPCGenerators_closure

theorem nativeFlagStabilizer_mem_directGeneratorClosure_of_fullPeel_mem
    {g : SplitOctF2Aut}
    (hg : g ∈ nativeFlagStabilizer)
    (hres : fullPeel g ∈ Subgroup.closure directFlagPCGenerators) :
    g ∈ Subgroup.closure directFlagPCGenerators := by
  obtain ⟨e, heq, _⟩ :=
    G2NativeFlagMatrixReadback.nativeFlagStabilizer_pcWord_residual_decomposition hg
  let H := Subgroup.closure directFlagPCGenerators
  have hpc : G2TwoSylowSubgroup.pcWord e ∈ H := by
    change G2TwoSylowSubgroup.pcWord e ∈
      Subgroup.closure directFlagPCGenerators
    rw [directFlagPCGenerators_closure_eq_unipotentSubgroup]
    exact ⟨e, rfl⟩
  rw [heq]
  exact H.mul_mem hpc hres

end InfoGeometry.Algebra.Zorn.G2NativeFlagGeneratorClosureBridge

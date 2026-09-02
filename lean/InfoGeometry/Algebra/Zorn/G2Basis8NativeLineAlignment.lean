import InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity
import InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback

/-!
# Alignment of the native base line with the eight-coordinate basis

The native line is indexed in `OctImF2`, whereas the automorphism carrier is
the eight-coordinate Boolean Zorn carrier.  This owner records only the
canonical three points that are actually used by the native base line.  In
the present coordinate order they are `basis8 4`, `basis8 5`, and their sum.
-/

namespace InfoGeometry.Algebra.Zorn.G2Basis8NativeLineAlignment

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.Zorn.G2NativeBaseFiber
open InfoGeometry.Algebra.Zorn.G2NativePointFoundation
open InfoGeometry.Algebra.Zorn.G2IntrinsicBaseFlag
open InfoGeometry.Algebra.Zorn.G2InvariantIncidenceCandidates
open InfoGeometry.Algebra.Zorn.G2NativeLineFiber
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerClosureReadback
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2NativeFlagStabilizerGenerators
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable section

def basis8Point4 : OctImIsotropicPoint :=
  ⟨nativeBasePoint, by native_decide⟩

def basis8Point5 : OctImIsotropicPoint :=
  ⟨baseLineVector, by native_decide⟩

def basis8Point45 : OctImIsotropicPoint :=
  ⟨nativeBasePoint + baseLineVector, by native_decide⟩

theorem basis8Point4_mem_baseIntrinsicLine :
    basis8Point4 ∈ baseIntrinsicLine.1 := by
  apply (mem_baseIntrinsicLine_iff basis8Point4).2
  change nativeBasePoint ∈ nativeBaseLineWitness
  simp [nativeBaseLineWitness, lineSet, nativeLineSetAt]

theorem basis8Point5_mem_baseIntrinsicLine :
    basis8Point5 ∈ baseIntrinsicLine.1 := by
  apply (mem_baseIntrinsicLine_iff basis8Point5).2
  change baseLineVector ∈ nativeBaseLineWitness
  simp [nativeBaseLineWitness, lineSet, nativeLineSetAt]

theorem basis8Point45_mem_baseIntrinsicLine :
    basis8Point45 ∈ baseIntrinsicLine.1 := by
  apply (mem_baseIntrinsicLine_iff basis8Point45).2
  change nativeBasePoint + baseLineVector ∈ nativeBaseLineWitness
  simp [nativeBaseLineWitness, lineSet, nativeLineSetAt]

theorem basis8Point4_zeroRelated_basis8Point5 :
    ZornZeroRelated basis8Point4 basis8Point5 := by
  native_decide +revert

theorem embed_octImPointPerm (g : SplitOctF2Aut)
    (p : OctImIsotropicPoint) :
    embed (octImPointPerm g p).1 = g⁻¹.1 (embed p.1) := by
  rw [octImPointPerm_apply]
  exact embed_octImAction g p.1

theorem embed_basis8Point4 :
    embed basis8Point4.1 = basis8 4 := by
  native_decide +revert

theorem embed_basis8Point5 :
    embed basis8Point5.1 = basis8 5 := by
  native_decide +revert

theorem embed_basis8Point45 :
    embed basis8Point45.1 = add (basis8 4) (basis8 5) := by
  native_decide +revert

theorem fullPeel_basis8_four_add_five_readback
    {g : SplitOctF2Aut}
    (hg : g ∈ G2NativeFlagStabilizerTransport.nativeFlagStabilizer) :
    (fullPeel g).1 (add (basis8 4) (basis8 5)) =
      add (basis8 4) (basis8 5) := by
  rw [automorphism_map_add, fullPeel_basis8_four_readback hg,
    fullPeel_basis8_five_readback hg]

theorem basis8Point4_action_readback (g : SplitOctF2Aut) :
    embed (octImPointPerm g basis8Point4).1 =
      g⁻¹.1 (basis8 4) := by
  rw [embed_octImPointPerm, embed_basis8Point4]

theorem basis8Point5_action_readback (g : SplitOctF2Aut) :
    embed (octImPointPerm g basis8Point5).1 =
      g⁻¹.1 (basis8 5) := by
  rw [embed_octImPointPerm, embed_basis8Point5]

theorem basis8Point45_action_readback (g : SplitOctF2Aut) :
    embed (octImPointPerm g basis8Point45).1 =
      g⁻¹.1 (add (basis8 4) (basis8 5)) := by
  rw [embed_octImPointPerm, embed_basis8Point45]

theorem basis8Point5_zeroRelated_basis8Point45 :
    ZornZeroRelated basis8Point5 basis8Point45 := by
  native_decide +revert

theorem basis8Point4_zeroRelated_basis8Point45 :
    ZornZeroRelated basis8Point4 basis8Point45 := by
  native_decide +revert

end
end InfoGeometry.Algebra.Zorn.G2Basis8NativeLineAlignment

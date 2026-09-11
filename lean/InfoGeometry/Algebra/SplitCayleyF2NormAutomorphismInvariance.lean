import InfoGeometry.Algebra.SplitCayleyF2DeltaNativeRelations
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.SplitCayleyF2NormCarrierAlignment
import InfoGeometry.Algebra.SplitCayleyF2NormStructural
import InfoGeometry.Algebra.SplitCayleyF2DeltaStructural
import InfoGeometry.Algebra.SL3NativeAutomorphismTransport
import InfoGeometry.Algebra.SplitCayleyF2NormGeneratorStructural

namespace InfoGeometry.Algebra.SplitCayleyF2

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints
open InfoGeometry.Algebra.Zorn.G2SplitOctZornCellBridge

theorem delta1NativeAutomorphism_norm (r : Vec3) (x : SplitOctF2) :
    zornNorm ((delta1NativeAutomorphism r).1 x) = zornNorm x := by
  let c : Cayley := cayleySplitOctF2Equiv.symm x
  have hc : cayleyToSplitOctF2 (delta1 r c) =
      (delta1NativeAutomorphism r).1 x := by
    have h := AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback
      (delta1AddMulAutomorphism r) x
    have h' := congrArg cayleySplitOctF2Equiv h
    simpa only [cayleyToSplitOctF2, delta1NativeAutomorphism,
      AddMulAutomorphism.toSplitOctF2Equiv, Equiv.apply_symm_apply] using h'.symm
  calc
    zornNorm ((delta1NativeAutomorphism r).1 x) =
        zornNorm (cayleyToSplitOctF2 (delta1 r c)) := by rw [hc]
    _ = zModToBool (norm (delta1 r c)) :=
      (cayley_norm_bool_readback (delta1 r c)).symm
    _ = zModToBool (norm c) := by rw [delta1_norm_structural]
    _ = zornNorm x := by
      rw [cayley_norm_bool_readback]
      exact congrArg zornNorm (Equiv.apply_symm_apply cayleySplitOctF2Equiv x)

theorem delta2NativeAutomorphism_norm (r : Vec3) (x : SplitOctF2) :
    zornNorm ((delta2NativeAutomorphism r).1 x) = zornNorm x := by
  let c : Cayley := cayleySplitOctF2Equiv.symm x
  have hc : cayleyToSplitOctF2 (delta2 r c) =
      (delta2NativeAutomorphism r).1 x := by
    have h := AddMulAutomorphism.toSplitOctF2Equiv_cayley_readback
      (delta2AddMulAutomorphism r) x
    have h' := congrArg cayleySplitOctF2Equiv h
    simpa only [cayleyToSplitOctF2, delta2NativeAutomorphism,
      AddMulAutomorphism.toSplitOctF2Equiv, Equiv.apply_symm_apply] using h'.symm
  calc
    zornNorm ((delta2NativeAutomorphism r).1 x) =
        zornNorm (cayleyToSplitOctF2 (delta2 r c)) := by rw [hc]
    _ = zModToBool (norm (delta2 r c)) :=
      (cayley_norm_bool_readback (delta2 r c)).symm
    _ = zModToBool (norm c) := by rw [delta2_norm_structural]
    _ = zornNorm x := by
      rw [cayley_norm_bool_readback]
      exact congrArg zornNorm (Equiv.apply_symm_apply cayleySplitOctF2Equiv x)

theorem cyclicNativeAutomorphism_norm (x : SplitOctF2) :
    zornNorm (cyclicNativeAutomorphism.1 x) = zornNorm x := by
  let c : Cayley := cayleySplitOctF2Equiv.symm x
  have hc : cayleyToSplitOctF2 (cyclicAction c) =
      cyclicNativeAutomorphism.1 x := by
    have h := cyclicNativeAutomorphism_cayley_readback x
    have h' := congrArg cayleySplitOctF2Equiv h
    simpa only [cayleyToSplitOctF2, c, Equiv.apply_symm_apply] using h'.symm
  calc
    zornNorm (cyclicNativeAutomorphism.1 x) =
        zornNorm (cayleyToSplitOctF2 (cyclicAction c)) := by rw [hc]
    _ = zModToBool (norm (cyclicAction c)) :=
      (cayley_norm_bool_readback (cyclicAction c)).symm
    _ = zModToBool (norm c) := by rw [cyclicAction_norm_structural]
    _ = zornNorm x := by
      rw [cayley_norm_bool_readback]
      exact congrArg zornNorm (Equiv.apply_symm_apply cayleySplitOctF2Equiv x)

theorem shearNativeAutomorphism_norm (x : SplitOctF2) :
    zornNorm (shearNativeAutomorphism.1 x) = zornNorm x := by
  let c : Cayley := cayleySplitOctF2Equiv.symm x
  have hc : cayleyToSplitOctF2 (shearAction c) =
      shearNativeAutomorphism.1 x := by
    have h := shearNativeAutomorphism_cayley_readback x
    have h' := congrArg cayleySplitOctF2Equiv h
    simpa only [cayleyToSplitOctF2, c, Equiv.apply_symm_apply] using h'.symm
  calc
    zornNorm (shearNativeAutomorphism.1 x) =
        zornNorm (cayleyToSplitOctF2 (shearAction c)) := by rw [hc]
    _ = zModToBool (norm (shearAction c)) :=
      (cayley_norm_bool_readback (shearAction c)).symm
    _ = zModToBool (norm c) := by rw [shearAction_norm_structural]
    _ = zornNorm x := by
      rw [cayley_norm_bool_readback]
      exact congrArg zornNorm (Equiv.apply_symm_apply cayleySplitOctF2Equiv x)

theorem delta1Native_isotropic_iff (r : Vec3) (x : SplitOctF2) :
    Isotropic ((delta1NativeAutomorphism r).1 x) ↔ Isotropic x := by
  change zornNorm ((delta1NativeAutomorphism r).1 x) = false ↔
    zornNorm x = false
  constructor
  · intro h
    rw [← delta1NativeAutomorphism_norm r x]
    exact h
  · intro h
    rw [delta1NativeAutomorphism_norm r x]
    exact h

theorem delta2Native_isotropic_iff (r : Vec3) (x : SplitOctF2) :
    Isotropic ((delta2NativeAutomorphism r).1 x) ↔ Isotropic x := by
  change zornNorm ((delta2NativeAutomorphism r).1 x) = false ↔
    zornNorm x = false
  constructor
  · intro h
    rw [← delta2NativeAutomorphism_norm r x]
    exact h
  · intro h
    rw [delta2NativeAutomorphism_norm r x]
    exact h

theorem cyclicNativeAutomorphism_isotropic_iff (x : SplitOctF2) :
    Isotropic (cyclicNativeAutomorphism.1 x) ↔ Isotropic x := by
  change zornNorm (cyclicNativeAutomorphism.1 x) = false ↔
    zornNorm x = false
  constructor
  · intro h
    rw [← cyclicNativeAutomorphism_norm x]
    exact h
  · intro h
    rw [cyclicNativeAutomorphism_norm x]
    exact h

theorem shearNativeAutomorphism_isotropic_iff (x : SplitOctF2) :
    Isotropic (shearNativeAutomorphism.1 x) ↔ Isotropic x := by
  change zornNorm (shearNativeAutomorphism.1 x) = false ↔
    zornNorm x = false
  constructor
  · intro h
    rw [← shearNativeAutomorphism_norm x]
    exact h
  · intro h
    rw [shearNativeAutomorphism_norm x]
    exact h

end InfoGeometry.Algebra.SplitCayleyF2

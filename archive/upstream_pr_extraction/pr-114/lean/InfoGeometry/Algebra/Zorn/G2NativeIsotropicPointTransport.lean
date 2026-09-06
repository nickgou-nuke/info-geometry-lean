import InfoGeometry.Algebra.Zorn.G2SplitOctNormComposition
import InfoGeometry.Algebra.SplitCayleyF2NormAutomorphismInvariance
import InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge

namespace InfoGeometry.Algebra.Zorn.G2NativeIsotropicPointTransport

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2FiniteIsotropicPoints
open InfoGeometry.Algebra.Zorn.G2ImaginaryOctImBridge
open InfoGeometry.Algebra.SplitCayleyF2

theorem isotropicPoints_mem_map_of_norm_iff
    (f : SplitOctF2Aut)
    (hNorm : ∀ X : SplitOctF2, zornNorm (f.1 X) = zornNorm X)
    (X : SplitOctF2) (hX : X ∈ isotropicPoints) :
    f.1 X ∈ isotropicPoints := by
  rw [mem_isotropicPoints] at hX ⊢
  constructor
  · change zornNorm (f.1 X) = false
    rw [hNorm]
    exact hX.1
  · intro hzero
    apply hX.2
    apply f.1.injective
    rw [hzero]
    change (zero : SplitOctF2) = f.1 zero
    rw [automorphism_map_zero]

theorem isotropicPoints_mem_map_iff_of_norm_iff
    (f : SplitOctF2Aut)
    (hNorm : ∀ X : SplitOctF2, zornNorm (f.1 X) = zornNorm X)
    (X : SplitOctF2) :
    f.1 X ∈ isotropicPoints ↔ X ∈ isotropicPoints := by
  constructor
  · intro h
    have h' := (mem_isotropicPoints (f.1 X)).mp h
    apply (mem_isotropicPoints X).mpr
    refine ⟨?_, ?_⟩
    · change zornNorm X = false
      have h'iso : zornNorm (f.1 X) = false := h'.1
      rw [← hNorm X]
      exact h'iso
    · intro hzero
      apply h'.2
      rw [hzero]
      change f.1 (InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.zero) =
        InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem.zero
      exact automorphism_map_zero f
  · exact isotropicPoints_mem_map_of_norm_iff f hNorm X

theorem delta1Native_isotropicPoints_mem
    (r : InfoGeometry.Algebra.SplitCayleyF2.Vec3)
    (X : SplitOctF2) (hX : X ∈ isotropicPoints) :
    (InfoGeometry.Algebra.SplitCayleyF2.delta1NativeAutomorphism r).1 X ∈
      isotropicPoints :=
  isotropicPoints_mem_map_of_norm_iff _
    (InfoGeometry.Algebra.SplitCayleyF2.delta1NativeAutomorphism_norm r) X hX

theorem delta2Native_isotropicPoints_mem
    (r : InfoGeometry.Algebra.SplitCayleyF2.Vec3)
    (X : SplitOctF2) (hX : X ∈ isotropicPoints) :
    (InfoGeometry.Algebra.SplitCayleyF2.delta2NativeAutomorphism r).1 X ∈
      isotropicPoints :=
  isotropicPoints_mem_map_of_norm_iff _
    (InfoGeometry.Algebra.SplitCayleyF2.delta2NativeAutomorphism_norm r) X hX

theorem cyclicNative_isotropicPoints_mem_iff (X : SplitOctF2) :
    cyclicNativeAutomorphism.1 X ∈ isotropicPoints ↔
      X ∈ isotropicPoints :=
  isotropicPoints_mem_map_iff_of_norm_iff _
    cyclicNativeAutomorphism_norm X

theorem shearNative_isotropicPoints_mem_iff (X : SplitOctF2) :
    shearNativeAutomorphism.1 X ∈ isotropicPoints ↔
      X ∈ isotropicPoints :=
  isotropicPoints_mem_map_iff_of_norm_iff _
    shearNativeAutomorphism_norm X

end InfoGeometry.Algebra.Zorn.G2NativeIsotropicPointTransport

import InfoGeometry.Lie.CanonicalZornDerivationCarrierEquiv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornMathlibRootSpace
import InfoGeometry.Lie.CanonicalZornTransportedRootEigenrelation

namespace InfoGeometry.Lie.CanonicalZornTransportedCartan

noncomputable section

open CanonicalZornDerivationCarrierEquiv
open CanonicalZornMathlibRootSpace
open CanonicalZornCartanRootSystem
open SplitOctonionAxialCartanErlangen
open CanonicalZornCartanAdjointRootDecomposition

abbrev NativeCartan := axialCartanLieSubalgebra
abbrev TransportedCartan :=
  NativeCartan.map nativeToMathlib.toLieHom

noncomputable def nativeToTransported :
    NativeCartan ≃ₗ⁅ℝ⁆ TransportedCartan := by
  let f : NativeCartan →ₗ⁅ℝ⁆ TransportedCartan :=
    { toFun := fun H =>
        ⟨nativeToMathlib H.1, by
          rw [LieSubalgebra.mem_map]
          exact ⟨H, H.2, rfl⟩⟩
      map_add' := by
        intro H K
        apply Subtype.ext
        rfl
      map_smul' := by
        intro r H
        apply Subtype.ext
        rfl
      map_lie' := by
        intro H K
        apply Subtype.ext
        rfl }
  apply LieEquiv.ofBijective f
  constructor
  · intro H K h
    have h' : nativeToMathlib H.1 = nativeToMathlib K.1 :=
      congrArg (fun X : TransportedCartan => X.1) h
    have hv : H.1 = K.1 := nativeToMathlib.injective h'
    exact Subtype.ext hv
  · intro H
    rcases (LieSubalgebra.mem_map nativeToMathlib.toLieHom NativeCartan H.1).mp H.2 with ⟨K, hK, hKH⟩
    refine ⟨⟨K, hK⟩, ?_⟩
    apply Subtype.ext
    exact hKH

@[simp] theorem nativeToTransported_apply (H : NativeCartan) :
    nativeToTransported H =
      ⟨nativeToMathlib H.1, by
        rw [LieSubalgebra.mem_map]
        exact ⟨H, H.2, rfl⟩⟩ := by
  rfl

def transportedRootWeight (i : nonzeroIndex) : TransportedCartan → ℝ :=
  fun H => nativeRootWeight i (nativeToTransported.symm H)

theorem rootDerivation_transported_eigenrelation (i : nonzeroIndex) :
    ∀ H : TransportedCartan,
      ⁅(H : Mathlib), nativeToMathlib (rootDerivation i.1)⁆ =
        transportedRootWeight i H • nativeToMathlib (rootDerivation i.1) := by
  intro H
  let K : NativeCartan := nativeToTransported.symm H
  have hK : nativeToTransported K = H := by
    simp [K]
  have hEigen :=
    CanonicalZornTransportedRootEigenrelation.rootDerivation_bracket_eigen
      i K
  have hbracket :
      ⁅(H : Mathlib), nativeToMathlib (rootDerivation i.1)⁆ =
        nativeRootWeight i K • nativeToMathlib (rootDerivation i.1) := by
    rw [← hK]
    change ⁅(nativeToMathlib (K : NativeCartan)),
        nativeToMathlib (rootDerivation i.1)⁆ = _
    simpa using hEigen
  exact hbracket

end
end InfoGeometry.Lie.CanonicalZornTransportedCartan

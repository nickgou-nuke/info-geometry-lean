import InfoGeometry.Quantum.GeometricTensorPolarizedPullback

/-!
# Rectangular bi-frame pullback

Unlike the endomorphism-valued pullback on one carrier, this construction
allows the source and target Hilbert carriers to be different.  It is the
operator-level form needed for a mixed pair of half-spin sectors.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Quantum.GeometricQuantumTensor

variable {𝕜 : Type*} [RCLike 𝕜]
variable {SPlus SMinus : Type*}
  [NormedAddCommGroup SPlus] [InnerProductSpace 𝕜 SPlus]
  [CompleteSpace SPlus]
  [NormedAddCommGroup SMinus] [InnerProductSpace 𝕜 SMinus]
  [CompleteSpace SMinus]

noncomputable def mixedPullback
    (Uplus : SPlus →L[𝕜] SPlus)
    (Uminus : SMinus →L[𝕜] SMinus)
    (G : SPlus →L[𝕜] SMinus) : SPlus →L[𝕜] SMinus :=
  (ContinuousLinearMap.adjoint Uminus).comp (G.comp Uplus)

theorem mixedPullback_apply
    (Uplus : SPlus →L[𝕜] SPlus)
    (Uminus : SMinus →L[𝕜] SMinus)
    (G : SPlus →L[𝕜] SMinus) (u : SPlus) (v : SMinus) :
    ⟪mixedPullback Uplus Uminus G u, v⟫_𝕜 =
      ⟪G (Uplus u), Uminus v⟫_𝕜 := by
  change ⟪ContinuousLinearMap.adjoint Uminus (G (Uplus u)), v⟫_𝕜 = _
  rw [ContinuousLinearMap.adjoint_inner_left]

end InfoGeometry.Quantum.GeometricQuantumTensor

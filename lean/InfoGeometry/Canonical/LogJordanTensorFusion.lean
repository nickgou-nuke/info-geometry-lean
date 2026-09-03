import InfoGeometry.Canonical.LogJordanVirasoroIntertwiner
import InfoGeometry.Canonical.ModularCoproductFlux

/-!
# InfoGeometry.Canonical.LogJordanTensorFusion

First categorical-algebraic bridge from the logarithmic Virasoro Jordan cell to
tensor-product fusion.

The owner theorem `ModularCoproductFlux.tensorJordanNilpotent_sq` proves that the
primitive tensor sum of two square-zero nilpotents

`N₁ ⊗ 1 + 1 ⊗ N₂`

has square `2 • (N₁ ⊗ N₂)` and cube zero.  This file instantiates that theorem
with the actual rank-two logarithmic Jordan nilpotent used by
`LogJordanVirasoroIntertwiner`.

Thus the tensor product of two rank-two logarithmic Jordan sectors has a
nilpotent contribution of order at most three.  This is the nearest formal DAG
edge toward a tensor-closed non-semisimple/logarithmic monoidal sector; no
braided-category packaging is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.LogJordanTensorFusion

open scoped TensorProduct

open InfoGeometry.Canonical.LogJordanVirasoroIntertwiner
open InfoGeometry.Canonical.ModularCoproductFlux

variable {𝕜 : Type*} [Field 𝕜]

abbrev JordanEnd (𝕜 : Type*) [Field 𝕜] := Matrix (Fin 2) (Fin 2) 𝕜

abbrev JordanTensorEnd (𝕜 : Type*) [Field 𝕜] :=
  JordanEnd 𝕜 ⊗[𝕜] JordanEnd 𝕜

/-- The primitive nilpotent part on the tensor product of two logarithmic
rank-two Jordan sectors. -/
def logTensorNilpotent : JordanTensorEnd 𝕜 :=
  tensorJordanNilpotent (R := 𝕜)
    (jordanNilpotent 𝕜) (jordanNilpotent 𝕜)

/-- The logarithmic Jordan generator used in each factor is square-zero. -/
theorem jordanNilpotent_sq_zero :
    jordanNilpotent 𝕜 * jordanNilpotent 𝕜 = 0 :=
  (zero_mode_subspace_indecomposable (𝕜 := 𝕜)).2

/-- Tensor fusion raises the possible Jordan depth: the square of the primitive
nilpotent is exactly the mixed tensor term. -/
theorem logTensorNilpotent_sq :
    logTensorNilpotent (𝕜 := 𝕜) * logTensorNilpotent (𝕜 := 𝕜) =
      (2 : 𝕜) •
        (jordanNilpotent 𝕜 ⊗ₜ[𝕜] jordanNilpotent 𝕜 : JordanTensorEnd 𝕜) := by
  simpa [logTensorNilpotent] using
    (tensorJordanNilpotent_sq (R := 𝕜)
      (jordanNilpotent 𝕜) (jordanNilpotent 𝕜)
      (jordanNilpotent_sq_zero (𝕜 := 𝕜))
      (jordanNilpotent_sq_zero (𝕜 := 𝕜)))

/-- The primitive tensor nilpotent of two rank-two logarithmic Jordan sectors
is nilpotent of order at most three. -/
theorem logTensorNilpotent_cube_zero :
    logTensorNilpotent (𝕜 := 𝕜) * logTensorNilpotent (𝕜 := 𝕜) *
        logTensorNilpotent (𝕜 := 𝕜) = 0 := by
  simpa [logTensorNilpotent] using
    (tensorJordanNilpotent_cube_zero (R := 𝕜)
      (jordanNilpotent 𝕜) (jordanNilpotent 𝕜)
      (jordanNilpotent_sq_zero (𝕜 := 𝕜))
      (jordanNilpotent_sq_zero (𝕜 := 𝕜)))

/-- The tensor-fusion nilpotent is the sum of the two factor nilpotents acting
on their respective tensor legs. -/
theorem logTensorNilpotent_eq :
    logTensorNilpotent (𝕜 := 𝕜) =
      (jordanNilpotent 𝕜 ⊗ₜ[𝕜] (1 : JordanEnd 𝕜)) +
      ((1 : JordanEnd 𝕜) ⊗ₜ[𝕜] jordanNilpotent 𝕜) := by
  rfl

end InfoGeometry.Canonical.LogJordanTensorFusion

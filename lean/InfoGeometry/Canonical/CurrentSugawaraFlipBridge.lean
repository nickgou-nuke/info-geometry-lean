import InfoGeometry.Canonical.CurrentSugawaraBridge

/-!
# Heisenberg orientation flip bridge

This file packages the algebra-level current flip

`J_n ↦ J_-n`, `K ↦ -K`

as a Lie algebra equivalence of the centrally extended Heisenberg algebra.
It is deliberately separate from the Sugawara readout file: the flip is the
structural input, while Sugawara remains the quadratic stress-tensor output.
-/

namespace InfoGeometry.Canonical.CurrentSugawaraFlipBridge

open VirasoroProject
open InfoGeometry.Canonical.CurrentSugawaraBridge

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The Heisenberg cocycle changes sign under the mode flip `n ↦ -n`. -/
lemma heisenbergCocycle_modeFlip
    (X Y : VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜) :
    VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (currentFlip (𝕜 := 𝕜) X) (currentFlip (𝕜 := 𝕜) Y) =
      - VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜 X Y := by
  apply LinearMap.ext_basis (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜)
    (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜)
  intro m n
  by_cases h : m + n = 0
  · have h' : (-m) + (-n) = 0 := by linarith
    simp [currentFlip_jgen, VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin_apply_jgen_jgen,
      h, h']
  · have h' : (-m) + (-n) ≠ 0 := by
      intro h0
      apply h
      linarith
    simp [currentFlip_jgen, VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin_apply_jgen_jgen,
      h, h']

/--
The Heisenberg orientation flip is the honest Lie algebra automorphism
`J_n ↦ J_-n`, `K ↦ -K`.
-/
noncomputable def heisenbergModeFlip :
    VirasoroProject.HeisenbergAlgebra 𝕜 ≃ₗ⁅𝕜⁆ VirasoroProject.HeisenbergAlgebra 𝕜 where
  toFun X := ⟨currentFlip (𝕜 := 𝕜) X.fst, -X.snd⟩
  invFun X := ⟨currentFlip (𝕜 := 𝕜) X.fst, -X.snd⟩
  map_add' := by
    intro X Y
    ext <;> simp [currentFlip]
  map_smul' := by
    intro c X
    ext <;> simp [currentFlip]
  map_lie' := by
    intro X Y
    ext <;> simp [VirasoroProject.HeisenbergAlgebra.bracket_def', heisenbergCocycle_modeFlip, currentFlip]
  left_inv := by
    intro X
    ext <;> simp [currentFlip]
  right_inv := by
    intro X
    ext <;> simp [currentFlip]

@[simp] lemma heisenbergModeFlip_jgen (n : ℤ) :
    heisenbergModeFlip (𝕜 := 𝕜) (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 n) =
      VirasoroProject.HeisenbergAlgebra.jgen 𝕜 (-n) := by
  ext <;> simp [heisenbergModeFlip, currentFlip_jgen]

@[simp] lemma heisenbergModeFlip_kgen :
    heisenbergModeFlip (𝕜 := 𝕜) (VirasoroProject.HeisenbergAlgebra.kgen 𝕜) =
      - VirasoroProject.HeisenbergAlgebra.kgen 𝕜 := by
  ext <;> simp [heisenbergModeFlip]

@[simp] lemma heisenbergModeFlip_bracket (X Y : VirasoroProject.HeisenbergAlgebra 𝕜) :
    heisenbergModeFlip (𝕜 := 𝕜) ⁅X, Y⁆ =
      ⁅heisenbergModeFlip (𝕜 := 𝕜) X, heisenbergModeFlip (𝕜 := 𝕜) Y⁆ := by
  simpa [heisenbergModeFlip] using
    (heisenbergModeFlip.map_lie' X Y)

end InfoGeometry.Canonical.CurrentSugawaraFlipBridge

import InfoGeometry.External.Virasoro.HeisenbergAlgebra

/-!
# Heisenberg orientation flip bridge

This file packages the full Heisenberg Lie-flip theorem on top of the
involutive current flip:

* `J_n ↦ J_-n`
* `K ↦ -K`

The current flip is the algebraic input; the Heisenberg lift is the Lie-level
orientation reversal.
-/

namespace InfoGeometry.Canonical.CurrentSugawaraFlipBridge

open VirasoroProject

variable {𝕜 : Type*} [Field 𝕜]

/-- Index reversal on the abelian current algebra. -/
noncomputable def currentFlip :
    VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜 ≃ₗ[𝕜] VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜 :=
  Finsupp.mapDomain.linearEquiv (M := 𝕜) (R := 𝕜) (Equiv.neg ℤ)

@[simp] lemma currentFlip_jgen (n : ℤ) :
    currentFlip (𝕜 := 𝕜) (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 n) =
      VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 (-n) := by
  change Finsupp.mapDomain (Equiv.neg ℤ) (Finsupp.single n (1 : 𝕜)) = _
  simp [VirasoroProject.AbelianLieAlgebraOn.jgen_eq_single]

@[simp] theorem currentFlip_involutive (X : VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜) :
    currentFlip (𝕜 := 𝕜) (currentFlip (𝕜 := 𝕜) X) = X := by
  simpa [currentFlip] using
    ((Finsupp.mapDomain_comp (f := Equiv.neg ℤ) (g := Equiv.neg ℤ) (v := X)).symm)

/-- The Heisenberg cocycle changes sign under mode reversal. -/
lemma heisenbergCocycle_modeFlip
    (X Y : VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜) :
    VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (currentFlip (𝕜 := 𝕜) X) (currentFlip (𝕜 := 𝕜) Y) =
      - VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜 X Y := by
  apply LinearMap.ext_basis (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜)
    (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜)
  intro m n
  simp [currentFlip_jgen,
    VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin_apply_jgen_jgen]
  by_cases h : m + n = 0
  · have h' : (-m) + (-n) = 0 := by linarith
    simp [h, h']
  · have h' : (-m) + (-n) ≠ 0 := by
      intro hh
      apply h
      linarith
    simp [h, h']

@[simp] theorem heisenbergCocycle_modeFlip_jgen
    (m n : ℤ) :
    VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (currentFlip (𝕜 := 𝕜) (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 m))
        (currentFlip (𝕜 := 𝕜) (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 n))
      =
    - VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 m)
        (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 n) := by
  simpa using heisenbergCocycle_modeFlip (𝕜 := 𝕜)
    (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 m)
    (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 n)

/--
The full Heisenberg orientation flip.

This is the honest Lie automorphism-level lift of the involutive current flip:
`Jₙ ↦ J₋ₙ` and `K ↦ -K`.
-/
noncomputable def heisenbergModeFlip :
    VirasoroProject.HeisenbergAlgebra 𝕜 ≃ₗ⁅𝕜⁆ VirasoroProject.HeisenbergAlgebra 𝕜 := by
  refine
    { toFun := fun X => ⟨currentFlip (𝕜 := 𝕜) X.fst, -X.snd⟩
      invFun := fun X => ⟨currentFlip (𝕜 := 𝕜) X.fst, -X.snd⟩
      map_add' := by
        intro X Y
        ext <;> simp [currentFlip]
      map_smul' := by
        intro c X
        ext <;> simp [currentFlip]
      left_inv := by
        intro X
        ext <;> simp [currentFlip]
      right_inv := by
        intro X
        ext <;> simp [currentFlip]
      map_lie' := by
        intro X Y
        apply VirasoroProject.HeisenbergAlgebra.ext'
        · simp [VirasoroProject.HeisenbergAlgebra.bracket_def']
        · simp [VirasoroProject.HeisenbergAlgebra.bracket_def', heisenbergCocycle_modeFlip] }

@[simp] theorem heisenbergModeFlip_jgen (n : ℤ) :
    heisenbergModeFlip (𝕜 := 𝕜) (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 n) =
      VirasoroProject.HeisenbergAlgebra.jgen 𝕜 (-n) := by
  apply VirasoroProject.HeisenbergAlgebra.ext'
  · simp [heisenbergModeFlip, currentFlip_jgen]
  · simp [heisenbergModeFlip]

@[simp] theorem heisenbergModeFlip_kgen :
    heisenbergModeFlip (𝕜 := 𝕜) (VirasoroProject.HeisenbergAlgebra.kgen 𝕜) =
      - VirasoroProject.HeisenbergAlgebra.kgen 𝕜 := by
  apply VirasoroProject.HeisenbergAlgebra.ext'
  · simp [heisenbergModeFlip]
  · simp [heisenbergModeFlip]

@[simp] theorem heisenbergModeFlip_involutive
    (X : VirasoroProject.HeisenbergAlgebra 𝕜) :
    heisenbergModeFlip (𝕜 := 𝕜) (heisenbergModeFlip (𝕜 := 𝕜) X) = X := by
  apply VirasoroProject.HeisenbergAlgebra.ext'
  · simp [heisenbergModeFlip, currentFlip_involutive]
  · simp [heisenbergModeFlip]

end InfoGeometry.Canonical.CurrentSugawaraFlipBridge

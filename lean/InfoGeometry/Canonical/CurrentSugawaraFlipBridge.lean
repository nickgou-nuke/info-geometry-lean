import InfoGeometry.External.Virasoro.HeisenbergAlgebra

/-!
# Heisenberg orientation flip bridge

This file isolates the generator-level sign reversal for the Heisenberg
cocycle under mode flip. It deliberately stops short of a full Sugawara
covariance theorem.
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

/-- Generator-level mode-flip sign on the Heisenberg cocycle. -/
@[simp] theorem heisenbergCocycle_modeFlip_jgen
    (m n : ℤ) :
    VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (currentFlip (𝕜 := 𝕜) (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 m))
        (currentFlip (𝕜 := 𝕜) (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 n))
      =
    - VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycleBilin 𝕜
        (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 m)
        (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 n) := by
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

end InfoGeometry.Canonical.CurrentSugawaraFlipBridge

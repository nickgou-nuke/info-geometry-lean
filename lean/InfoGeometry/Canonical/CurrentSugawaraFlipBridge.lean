import InfoGeometry.External.Virasoro.HeisenbergModeFlip

/-!
# Heisenberg orientation flip bridge

This file packages the external orientation-reversal theorem under the
canonical bridge namespace. It re-exports the owner surface with the canonical
names used elsewhere in the repo.
-/

namespace InfoGeometry.Canonical.CurrentSugawaraFlipBridge

open VirasoroProject
open Module

noncomputable section

variable {𝕜 : Type*} [Field 𝕜]

/-- Index reversal on the abelian current algebra. -/
abbrev currentFlip :
    VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜 →ₗ[𝕜]
      VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜 :=
  VirasoroProject.AbelianLieAlgebraOn.modeFlip 𝕜

@[simp] theorem currentFlip_jgen (n : ℤ) :
    currentFlip (𝕜 := 𝕜) (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 n) =
      VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 (-n) := by
  simpa [currentFlip] using
    (VirasoroProject.AbelianLieAlgebraOn.modeFlip_jgen (𝕜 := 𝕜) n)

@[simp] theorem currentFlip_involutive (X : VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜) :
    currentFlip (𝕜 := 𝕜) (currentFlip (𝕜 := 𝕜) X) = X := by
  have h := congrArg (fun f : VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜 →ₗ[𝕜]
      VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜 => f X)
    (VirasoroProject.AbelianLieAlgebraOn.modeFlip_involutive (𝕜 := 𝕜))
  simpa [currentFlip] using h

section Heisenberg

variable [CharZero 𝕜]

/-- Orientation reversal on the centrally extended Heisenberg algebra. -/
abbrev heisenbergModeFlip :
    VirasoroProject.HeisenbergAlgebra 𝕜 →ₗ[𝕜] VirasoroProject.HeisenbergAlgebra 𝕜 :=
  VirasoroProject.HeisenbergAlgebra.modeFlip 𝕜

@[simp] theorem heisenbergModeFlip_jgen
    (n : ℤ) :
    heisenbergModeFlip (𝕜 := 𝕜) (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 n) =
      VirasoroProject.HeisenbergAlgebra.jgen 𝕜 (-n) := by
  simpa [heisenbergModeFlip] using
    (VirasoroProject.HeisenbergAlgebra.modeFlip_jgen (𝕜 := 𝕜) n)

@[simp] theorem heisenbergModeFlip_kgen :
    heisenbergModeFlip (𝕜 := 𝕜) (VirasoroProject.HeisenbergAlgebra.kgen 𝕜) =
      - VirasoroProject.HeisenbergAlgebra.kgen 𝕜 := by
  simpa [heisenbergModeFlip] using
    (VirasoroProject.HeisenbergAlgebra.modeFlip_kgen (𝕜 := 𝕜))

@[simp] theorem heisenbergModeFlip_involutive
    (X : VirasoroProject.HeisenbergAlgebra 𝕜) :
    heisenbergModeFlip (𝕜 := 𝕜) (heisenbergModeFlip (𝕜 := 𝕜) X) = X := by
  have h := congrArg (fun f : VirasoroProject.HeisenbergAlgebra 𝕜 →ₗ[𝕜]
      VirasoroProject.HeisenbergAlgebra 𝕜 => f X)
    (VirasoroProject.HeisenbergAlgebra.modeFlip_comp_modeFlip (𝕜 := 𝕜))
  simpa [heisenbergModeFlip] using h

/-- The canonical Heisenberg Lie homomorphism corresponding to mode reversal. -/
abbrev heisenbergModeFlipLieHom :
    VirasoroProject.HeisenbergAlgebra 𝕜 →ₗ⁅𝕜⁆ VirasoroProject.HeisenbergAlgebra 𝕜 :=
  VirasoroProject.HeisenbergAlgebra.modeFlipLieHom 𝕜

end Heisenberg

end
end InfoGeometry.Canonical.CurrentSugawaraFlipBridge

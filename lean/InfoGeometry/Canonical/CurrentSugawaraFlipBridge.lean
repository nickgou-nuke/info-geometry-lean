/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.External.Virasoro.HeisenbergModeFlip
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Heisenberg Orientation Flip Bridge

This module provides the canonical orientation-reversal maps `currentFlip` on
`AbelianLieAlgebraOn ℤ 𝕜` and `heisenbergModeFlip` / `heisenbergModeFlipLieHom`
on `HeisenbergAlgebra 𝕜`, and proves their action on the generators `jgen n` and
`kgen` together with involutivity `currentFlip (currentFlip X) = X` and
`heisenbergModeFlip (heisenbergModeFlip X) = X`.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.External.Virasoro.HeisenbergModeFlip`:
    `AbelianLieAlgebraOn.modeFlip`, `HeisenbergAlgebra.modeFlip`,
    `HeisenbergAlgebra.modeFlipLieHom`.
- BUCKET 2 (Deconfabulation):
  * All generator evaluations and involutivity theorems are proved via explicit
    unfolding and linear map congruence.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `currentFlip`, `heisenbergModeFlip`, `heisenbergModeFlipLieHom`.
  * `currentFlip_jgen`, `currentFlip_involutive`,
    `heisenbergModeFlip_jgen`, `heisenbergModeFlip_kgen`,
    `heisenbergModeFlip_involutive`.
-/

namespace InfoGeometry.Canonical.CurrentSugawaraFlipBridge

open VirasoroProject
open Module

noncomputable section

variable {𝕜 : Type*} [Field 𝕜]

/-- Index reversal linear map on the abelian current algebra `AbelianLieAlgebraOn ℤ 𝕜`. -/
def currentFlip :
    VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜 →ₗ[𝕜]
      VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜 :=
  VirasoroProject.AbelianLieAlgebraOn.modeFlip 𝕜

/-- `currentFlip` sends `jgen n` to `jgen (-n)`. -/
@[simp] theorem currentFlip_jgen (n : ℤ) :
    currentFlip (𝕜 := 𝕜) (VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 n) =
      VirasoroProject.AbelianLieAlgebraOn.jgen 𝕜 (-n) := by
  unfold currentFlip
  exact VirasoroProject.AbelianLieAlgebraOn.modeFlip_jgen (𝕜 := 𝕜) n

/-- `currentFlip` is involutive on `AbelianLieAlgebraOn ℤ 𝕜`. -/
@[simp] theorem currentFlip_involutive (X : VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜) :
    currentFlip (𝕜 := 𝕜) (currentFlip (𝕜 := 𝕜) X) = X := by
  have h := congrArg (fun f : VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜 →ₗ[𝕜]
      VirasoroProject.AbelianLieAlgebraOn ℤ 𝕜 => f X)
    (VirasoroProject.AbelianLieAlgebraOn.modeFlip_involutive (𝕜 := 𝕜))
  unfold currentFlip
  exact h

section Heisenberg

variable [CharZero 𝕜]

/-- Orientation reversal linear map on the centrally extended Heisenberg algebra. -/
def heisenbergModeFlip :
    VirasoroProject.HeisenbergAlgebra 𝕜 →ₗ[𝕜] VirasoroProject.HeisenbergAlgebra 𝕜 :=
  VirasoroProject.HeisenbergAlgebra.modeFlip 𝕜

/-- `heisenbergModeFlip` sends `jgen n` to `jgen (-n)`. -/
@[simp] theorem heisenbergModeFlip_jgen
    (n : ℤ) :
    heisenbergModeFlip (𝕜 := 𝕜) (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 n) =
      VirasoroProject.HeisenbergAlgebra.jgen 𝕜 (-n) := by
  unfold heisenbergModeFlip
  exact VirasoroProject.HeisenbergAlgebra.modeFlip_jgen (𝕜 := 𝕜) n

/-- `heisenbergModeFlip` negates the central generator `kgen`. -/
@[simp] theorem heisenbergModeFlip_kgen :
    heisenbergModeFlip (𝕜 := 𝕜) (VirasoroProject.HeisenbergAlgebra.kgen 𝕜) =
      - VirasoroProject.HeisenbergAlgebra.kgen 𝕜 := by
  unfold heisenbergModeFlip
  exact VirasoroProject.HeisenbergAlgebra.modeFlip_kgen (𝕜 := 𝕜)

/-- `heisenbergModeFlip` is involutive on `HeisenbergAlgebra 𝕜`. -/
@[simp] theorem heisenbergModeFlip_involutive
    (X : VirasoroProject.HeisenbergAlgebra 𝕜) :
    heisenbergModeFlip (𝕜 := 𝕜) (heisenbergModeFlip (𝕜 := 𝕜) X) = X := by
  have h := congrArg (fun f : VirasoroProject.HeisenbergAlgebra 𝕜 →ₗ[𝕜]
      VirasoroProject.HeisenbergAlgebra 𝕜 => f X)
    (VirasoroProject.HeisenbergAlgebra.modeFlip_comp_modeFlip (𝕜 := 𝕜))
  unfold heisenbergModeFlip
  exact h

/-- The canonical Heisenberg Lie homomorphism corresponding to mode reversal. -/
def heisenbergModeFlipLieHom :
    VirasoroProject.HeisenbergAlgebra 𝕜 →ₗ⁅𝕜⁆ VirasoroProject.HeisenbergAlgebra 𝕜 :=
  VirasoroProject.HeisenbergAlgebra.modeFlipLieHom 𝕜

end Heisenberg

end

end InfoGeometry.Canonical.CurrentSugawaraFlipBridge

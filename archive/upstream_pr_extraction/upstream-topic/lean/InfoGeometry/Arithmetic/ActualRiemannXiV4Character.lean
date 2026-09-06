import InfoGeometry.Arithmetic.RiemannXiV4CharacterBridge
import InfoGeometry.Topology.ActualEntireXiFunctionDatumBridge

/-!
# The actual entire completed-Xi V₄ character readout

This file specializes the abstract reflection-character packet to the native
pole-removed `entireRiemannXi`.  It does not introduce a Hardy `Z` function,
Riemann--Siegel phase, zero-location result, or spectral interpretation.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ActualRiemannXiV4Character

open InfoGeometry.Arithmetic.RiemannXiV4CharacterBridge
open InfoGeometry.Arithmetic.ActualRiemannXiEntireBridge
open InfoGeometry.Topology.ActualEntireXiFunctionDatumBridge

theorem entireRiemannXi_V4_character_packet (u τ : ℝ) :
    xiRealCharacter ActualRiemannXiEntireBridge.entireRiemannXi (-u) τ =
        xiRealCharacter ActualRiemannXiEntireBridge.entireRiemannXi u τ ∧
      xiRealCharacter ActualRiemannXiEntireBridge.entireRiemannXi u (-τ) =
        xiRealCharacter ActualRiemannXiEntireBridge.entireRiemannXi u τ ∧
      xiImagCharacter ActualRiemannXiEntireBridge.entireRiemannXi (-u) τ =
        -xiImagCharacter ActualRiemannXiEntireBridge.entireRiemannXi u τ ∧
      xiImagCharacter ActualRiemannXiEntireBridge.entireRiemannXi u (-τ) =
        -xiImagCharacter ActualRiemannXiEntireBridge.entireRiemannXi u τ := by
  exact xiV4_character_packet ActualRiemannXiEntireBridge.entireRiemannXi
    actualEntireRiemannXiFunctionDatum u τ

theorem entireRiemannXi_imag_on_critical_line (τ : ℝ) :
    xiImagCharacter ActualRiemannXiEntireBridge.entireRiemannXi 0 τ = 0 := by
  exact xiImag_on_critical_line ActualRiemannXiEntireBridge.entireRiemannXi
    actualEntireRiemannXiFunctionDatum τ

end InfoGeometry.Arithmetic.ActualRiemannXiV4Character

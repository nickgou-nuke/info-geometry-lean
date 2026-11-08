/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.MajoranaSheetConnectors
import InfoGeometry.Canonical.KreinMajoranaZeroModeBlock
import InfoGeometry.Quantum.RealSplitClifford

/-!
# Majorana sheet kernels and KKT projector sectors

On the canonical doubled real carrier, identify the fixed spaces of the
KKT-core zero/cozero projectors with the positive/negative epsilon sheets.
The concrete split-null CAR kernels then coincide with these projector fixed
spaces. The projector names describe grading sectors here; this module does
not assert a Hamiltonian zero mode or a physical spectral statement.
-/

namespace InfoGeometry.Krein.MajoranaKernelProjectorBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Krein.PolarizedSector
open InfoGeometry.Canonical.KKTCore
open InfoGeometry.Canonical.KreinMajoranaZeroModeBlock
open InfoGeometry.Canonical.MajoranaPHSZeroMode
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Quantum

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- The KKT-core zero-mode projector fixed space is the positive epsilon sheet.
The `zeroModeProjector` is the grading projector from `KKTCore`. -/
theorem zeroModeProjector_fixed_iff_plusSheet (u : H₂) :
    zeroModeProjector (doubledSpaceCl11Action (E := E)) u = u ↔
      u ∈ plusSheet (E := E) := by
  change spectralPlusProj (E := E) u = u ↔ u ∈ plusSheet (E := E)
  rw [spectralPlusProj_apply_eq_plusPoint]
  constructor
  · intro hu
    rw [← hu]
    exact plusPoint_mem_plusSheet (E := E) (WithLp.fst u)
  · intro hu
    exact (eq_plusPoint_of_mem_plusSheet hu).symm

/-- The KKT-core cozero projector fixed space is the negative epsilon sheet. -/
theorem cozeroModeProjector_fixed_iff_minusSheet (u : H₂) :
    cozeroModeProjector (doubledSpaceCl11Action (E := E)) u = u ↔
      u ∈ minusSheet (E := E) := by
  change spectralMinusProj (E := E) u = u ↔ u ∈ minusSheet (E := E)
  rw [spectralMinusProj_apply_eq_minusPoint]
  constructor
  · intro hu
    rw [← hu]
    exact minusPoint_mem_minusSheet (E := E) (WithLp.snd u)
  · intro hu
    exact (eq_minusPoint_of_mem_minusSheet hu).symm

/-- Creation's vector kernel is exactly the fixed space of the canonical
KKT-core zero-mode projector. -/
theorem creation_kernel_iff_zeroModeProjector_fixed (u : H₂) :
    InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARCreation
        (E := E) u = 0 ↔
      zeroModeProjector (doubledSpaceCl11Action (E := E)) u = u := by
  rw [InfoGeometry.Krein.MajoranaSheetConnectors.creation_kernel_iff_plusSheet,
    zeroModeProjector_fixed_iff_plusSheet]

/-- Annihilation's vector kernel is exactly the fixed space of the canonical
KKT-core cozero projector. -/
theorem annihilation_kernel_iff_cozeroModeProjector_fixed (u : H₂) :
    InfoGeometry.Canonical.SuperchargeCARCCRBridge.concreteCARAnnihilation
        (E := E) u = 0 ↔
      cozeroModeProjector (doubledSpaceCl11Action (E := E)) u = u := by
  rw [InfoGeometry.Krein.MajoranaSheetConnectors.annihilation_kernel_iff_minusSheet,
    cozeroModeProjector_fixed_iff_minusSheet]

end Core

end InfoGeometry.Krein.MajoranaKernelProjectorBridge

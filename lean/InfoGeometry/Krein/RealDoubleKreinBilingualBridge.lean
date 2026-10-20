/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.HestenesMoebiusKreinBilingualBridge

/-!
# Real doubled-Krein readout for the Hestenes coordinate carrier

The Hestenes coordinate carrier and the native `DoubledSpace` carrier are
different types.  This file records the concrete coordinate readout between
them and proves the operator laws transported by that readout.  In
particular, the sheet swap and the grading are involutions, while their
composition is the quarter-turn with square `-1`.
-/

namespace InfoGeometry.Krein.Bilingual

open InfoGeometry.Krein

section Core

/-- Read a Hestenes coordinate pair as a native real doubled state. -/
def hestenesReadout (v : HestenesVector) : DoubledSpace ℝ :=
  to_doubled v.x v.y

/-- The coordinate sheet swap corresponding to `modular_j`. -/
def hestenesSheetSwap (v : HestenesVector) : HestenesVector :=
  ⟨v.y, v.x⟩

/-- The coordinate grading corresponding to `spectral_epsilon`. -/
def hestenesGrading (v : HestenesVector) : HestenesVector :=
  ⟨v.x, -v.y⟩

/-- The coordinate quarter-turn corresponding to `complex_i`. -/
def hestenesQuarterTurn (v : HestenesVector) : HestenesVector :=
  ⟨-v.y, v.x⟩

@[simp]
theorem modular_j_hestenesReadout (v : HestenesVector) :
    modular_j (hestenesReadout v) = hestenesReadout (hestenesSheetSwap v) := by
  apply DoubledSpace.ext <;> simp [hestenesReadout, hestenesSheetSwap]

@[simp]
theorem spectral_epsilon_hestenesReadout (v : HestenesVector) :
    spectral_epsilon (hestenesReadout v) = hestenesReadout (hestenesGrading v) := by
  apply DoubledSpace.ext <;> simp [hestenesReadout, hestenesGrading]

@[simp]
theorem complex_i_hestenesReadout (v : HestenesVector) :
    complex_i (hestenesReadout v) = hestenesReadout (hestenesQuarterTurn v) := by
  apply DoubledSpace.ext <;> simp [hestenesReadout, hestenesQuarterTurn]

theorem hestenesSheetSwap_involutive (v : HestenesVector) :
    hestenesSheetSwap (hestenesSheetSwap v) = v := by
  cases v
  rfl

theorem hestenesGrading_involutive (v : HestenesVector) :
    hestenesGrading (hestenesGrading v) = v := by
  cases v
  simp [hestenesGrading]

theorem hestenesQuarterTurn_sq (v : HestenesVector) :
    hestenesQuarterTurn (hestenesQuarterTurn v) = ⟨-v.x, -v.y⟩ := by
  cases v
  rfl

end Core

end InfoGeometry.Krein.Bilingual

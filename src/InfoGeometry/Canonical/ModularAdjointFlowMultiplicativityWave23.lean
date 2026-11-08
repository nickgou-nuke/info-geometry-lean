/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.Cl11LorentzAction

/- SPDX-License-Identifier: Apache-2.0 -/

/-!
# Multiplicativity of the finite Cl(1,1) modular adjoint flow

This closes the operator-algebraic action law for the existing `Cl11LorentzAction`
carrier.  It proves multiplicativity of the actual conjugation map; no new
carrier, wrapper, or supplied witness is introduced.
-/

namespace InfoGeometry.Canonical.Cl11LorentzAction

open InfoGeometry.Canonical.KKTCore
open KKTLorentzOrbitBridge
open InfoGeometry.Quantum

section Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "EndH" => H →L[ℝ] H

/-- The finite modular adjoint flow preserves operator multiplication. -/
@[rep_depth transport]
theorem modularAdjointFlow_mul
    (X : RealSplitCl11Action H) (t : ℝ) (A B : EndH) :
    modularAdjointFlow X t (A * B) =
      modularAdjointFlow X t A * modularAdjointFlow X t B := by
  unfold modularAdjointFlow
  calc
    modularFlow X t * (A * B) * modularFlow X (-t) =
        (modularFlow X t * A) * (B * modularFlow X (-t)) := by
      simp only [mul_assoc]
    _ = (modularFlow X t * A) *
          (modularFlow X (-t) * modularFlow X t) *
          (B * modularFlow X (-t)) := by
      rw [modularFlow_neg_mul_modularFlow (X := X) (t := t)]
      simp
    _ = (modularFlow X t * A * modularFlow X (-t)) *
          (modularFlow X t * B * modularFlow X (-t)) := by
      simp only [mul_assoc]
    _ = modularAdjointFlow X t A * modularAdjointFlow X t B := by
      rfl

end Core

end InfoGeometry.Canonical.Cl11LorentzAction

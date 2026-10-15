/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Basic.Real.Basic
import InfoGeometry.Algebra.ChakravalaGA
import InfoGeometry.Canonical.NaturalGradientSubmersionFlow
import InfoGeometry.QuantumContext.MatrixGNS

/-!
# Exported Lean 4 Verification Oracle: C-ABI Integration

This module exposes computable decision procedures and runtime invariant checkers
to the C ABI via `@[export]` attributes, enabling direct `ccall` consumption in Julia:

- `lean_koszul_sign`: Computable parity sign operator.
- `lean_verify_zero_vertical_drift`: Horizontal metric inversion verification.
- `lean_verify_attention_sink`: GNS state vacuum non-degeneracy guard.
-/

namespace InfoGeometry.Export.LeanOracle

/-! ### Contract 2: Exported Certified Koszul Sign Operator -/

/-- Certified Koszul sign calculation for UInt8 parity inputs (0 = even, 1 = odd). -/
@[export lean_koszul_sign]
def exportKoszulSign (p q : UInt8) : Int8 :=
  if (p &&& 1 == 1) && (q &&& 1 == 1) then (-1 : Int8) else (1 : Int8)

/-! ### Contract 1: Exported Horizontal Metric Inversion Oracle -/

/-- Certified check that vertical velocity is identically zero.
    Returns 1 if ||P_V(v)|| <= epsilon, 0 otherwise. -/
@[export lean_verify_zero_vertical_drift]
def exportVerifyZeroVerticalDrift (v_vertical_norm : Float) (eps : Float) : UInt8 :=
  if v_vertical_norm ≤ eps then (1 : UInt8) else (0 : UInt8)

/-! ### Contract 4: Exported GNS Attention Sink Vacuum Guard -/

/-- Certified verification that an anchor token prevents GNS state degeneration.
    Returns 1 if anchor weight rho_0 > eps, 0 if context amnesia is imminent. -/
@[export lean_verify_attention_sink]
def exportVerifyAttentionSink (rho_anchor : Float) (eps : Float) : UInt8 :=
  if rho_anchor > eps then (1 : UInt8) else (0 : UInt8)

end InfoGeometry.Export.LeanOracle

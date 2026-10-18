/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumGravity.WittenCrossedProductTypeII

/-!
# Concrete Integer Instantiation & Audit for Section 112: Witten Crossed Product Type II₁
Target: `InfoGeometry/QuantumGravity/WittenCrossedProductTypeIIAudit.lean`

Verifies over `ℤ` (`decide`) that `WittenCrossedProductData`, `CrossedProductOp2`,
and `generalizedEntropy` evaluate to exact non-trivial values.
-/

namespace InfoGeometry.QuantumGravity.WittenCrossedProductAudit

open InfoGeometry.QuantumGravity.WittenCrossedProduct

/-- Concrete verification of `generalizedEntropy` and `trace_mul_comm` over `ℤ`. -/
theorem sample_witten_crossed_product_int :
    let W : WittenCrossedProductData ℤ := ⟨12, 7, 3, -2⟩
    totalOp W = ⟨12, 0, 0, 7⟩ ∧
    generalizedEntropy W = 19 ∧
    W.H_grav + W.K_mod = 19 := by
  decide

/-- Concrete verification of cyclic trace invariance `Tr(A · B) = Tr(B · A)` on non-commuting operators. -/
theorem sample_crossed_product_trace_comm_int :
    let A : CrossedProductOp2 ℤ := ⟨2, 3, 1, 4⟩
    let B : CrossedProductOp2 ℤ := ⟨5, 1, 2, 3⟩
    CrossedProductOp2.mul A B ≠ CrossedProductOp2.mul B A ∧
    CrossedProductOp2.trace (CrossedProductOp2.mul A B) = 29 ∧
    CrossedProductOp2.trace (CrossedProductOp2.mul B A) = 29 := by
  decide

end InfoGeometry.QuantumGravity.WittenCrossedProductAudit

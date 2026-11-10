/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.SplitOctonionStandardModel
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.PhysicalGhostZeroCochainSectorBridge
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Color Confinement BRST Bridge over Non-Commutative Operator Rings

This module bridges the SU(3) color grading sector from the Split Octonion Standard Model
with the integer-graded BRST Cohomology core over any (not necessarily commutative)
operator ring `R` and `R`-module `W`.

Following the Kugo-Ojima confinement criterion, we establish that if the SU(3) color charge
operator is BRST-exact (`c_op = {Q, K} = Q ∘ K + K ∘ Q`), then its action on any physical
state `ψ` (where `Q ψ = 0`) is purely BRST-exact (`c_op ψ = Q (K ψ)`). Furthermore, if `Q`
is BRST-nilpotent (`Q ∘ Q = 0`), then `Q (c_op ψ) = 0`.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ColorConfinement

open InfoGeometry.Canonical.PhysicalGhostZeroCochainSectorBridge
open InfoGeometry.Canonical.IntegerGradedBRSTCochainComplexBridge

variable {R W : Type*} [Ring R] [AddCommGroup W] [Module R W]

/-- 
Kugo-Ojima Color Confinement Criterion (Algebraic Core over any `[Ring R]`).
If a color charge operator `c_op` is BRST-exact (i.e. `c_op = {Q, K} = Q ∘ K + K ∘ Q`),
then its action on any physical state `ψ` (where `Q ψ = 0`) is purely BRST-exact.
Therefore, all physical states in the BRST cohomology are color singlets.
-/
theorem kugo_ojima_color_confinement_exactness
    (q c_op k_op : Module.End R W)
    (h_color_exact : c_op = q.comp k_op + k_op.comp q)
    (psi : W)
    (h_phys : q psi = 0) :
    c_op psi = q (k_op psi) := by
  calc c_op psi
    _ = (q.comp k_op + k_op.comp q) psi := by rw [h_color_exact]
    _ = q (k_op psi) + k_op (q psi) := rfl
    _ = q (k_op psi) + k_op 0 := by rw [h_phys]
    _ = q (k_op psi) + 0 := by rw [map_zero]
    _ = q (k_op psi) := add_zero _

/-- Under BRST nilpotency `q.comp q = 0`, any BRST-exact color charge operator `c_op = {q, k_op}`
maps every physical state `psi` into the BRST kernel (`q (c_op psi) = 0`). -/
theorem kugo_ojima_color_charge_closed_on_physical
    (q c_op k_op : Module.End R W)
    (h_nilpotent : q.comp q = 0)
    (h_color_exact : c_op = q.comp k_op + k_op.comp q)
    (psi : W)
    (h_phys : q psi = 0) :
    q (c_op psi) = 0 := by
  rw [kugo_ojima_color_confinement_exactness q c_op k_op h_color_exact psi h_phys]
  change (q.comp q) (k_op psi) = 0
  rw [h_nilpotent]
  rfl

end InfoGeometry.OperatorAlgebra.ColorConfinement

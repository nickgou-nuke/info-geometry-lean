/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.NCG.CategoricalColimitStateDescent

/-!
# KMS state transport to the lower stage

The existing sequential colimit owner proves pullback of a KMS equation at a
later stage, but leaves the conclusion expressed with one product still at
that later stage.  This file closes that interface: state compatibility and
flow intertwining transport the complete KMS boundary equation back to the
original stage.
-/

noncomputable section

namespace InfoGeometry.NCG.DirectSystem.ModularFlowCocone

open InfoGeometry.NCG

variable {R : Type*} [CommRing R]
variable {S : DirectSystem R}

theorem kms_condition_transitionN_pullback_to_stage
    (C : DirectSystem.StateCocone S)
    (M : DirectSystem.ModularFlowCocone S)
    (n k : ℕ) (a b : S.Stage n)
    (h_kms :
      C.state (n + k)
          (S.transitionN n k a * M.flow (n + k) (S.transitionN n k b)) =
        C.state (n + k)
          (S.transitionN n k b * S.transitionN n k a)) :
    C.state n (a * M.flow n b) = C.state n (b * a) := by
  rw [← C.state_transitionN n k (a * M.flow n b)]
  rw [← C.state_transitionN n k (b * a)]
  rw [S.transitionN_mul, S.transitionN_mul]
  rw [← M.flow_transitionN]
  exact h_kms

end InfoGeometry.NCG.DirectSystem.ModularFlowCocone

end noncomputable section

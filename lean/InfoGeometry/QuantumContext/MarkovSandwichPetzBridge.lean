/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovSandwichFourCornerK0
import InfoGeometry.QuantumContext.MarkovGroupInversePetzCorner

/-!
# Two-sided Markov group inverse as Petz compression

The regular idempotent of the two-sided Markov sandwich action is the same
operator as compression by the Markov range idempotent. This identifies the
existing four-corner operator with the repository's algebraic Petz recovery
map on the full matrix carrier.
-/

namespace InfoGeometry.QuantumContext.MarkovSandwichPetzBridge

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.QuantumContext.MarkovDrazin
open InfoGeometry.QuantumContext.MarkovMatrixFourCornerK0
open InfoGeometry.QuantumContext.MarkovSandwichFourCornerK0
open InfoGeometry.QuantumContext.PetzMartingale

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Applying the regular idempotent of the two-sided Markov action is exactly
the algebraic Petz compression by the one-sided Markov range idempotent. -/
theorem markovSandwich_regularIdempotent_apply_eq_petzRecovery
    (P G X : MatrixCarrier (ι := ι))
    (hG : IsGroupInverse ((1 : MatrixCarrier (ι := ι)) - P) G) :
    regularIdempotent (cornerMap (1 - P) (1 - P)) (cornerMap G G) X =
      petzRecovery (markovRangeIdempotent P G) X := by
  change cornerMap (1 - P) (1 - P) (cornerMap G G X) = _
  simp only [cornerMap_apply, markovRangeIdempotent, petzRecovery]
  calc
    (1 - P) * (G * (X * G) * (1 - P)) =
        ((1 - P) * G) * X * (G * (1 - P)) := by noncomm_ring
    _ = ((1 - P) * G) * X * ((1 - P) * G) := by rw [← hG.2.2]

end InfoGeometry.QuantumContext.MarkovSandwichPetzBridge

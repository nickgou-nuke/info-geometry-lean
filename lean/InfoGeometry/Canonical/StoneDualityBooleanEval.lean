import Mathlib
import InfoGeometry.Canonical.UHFBooleanProjectionCantorBridge

/-!
# Stone duality for the Cantor boundary

This is the repo-owned Stone layer in canonical theorem form.
It does not introduce a new topological theorem. It only re-exports the
already-verified Cantor/Stone evaluation and principal-boundary recovery
lemmas from the UHF Boolean projection bridge.
-/

noncomputable section

namespace InfoGeometry.Canonical.StoneDualityBooleanEval

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFBooleanProjectionCantorBridge

/-- Cantor boundary evaluation is exactly the Stone prefix membership test. -/
theorem cantor_eval_true_iff_pointStoneFilter
    (x : CantorBoundary) (n : ℕ) (A : FiniteBooleanAlgebra n) :
    cantorBooleanEvaluation x n A = true ↔ A ∈ pointStoneFilter x n :=
  cantorBooleanEvaluation_eq_true_iff_pointStoneFilter x n A

/-- A Cantor Stone ultrafilter recovers its boundary point. -/
theorem cantor_principal_toBoundary (x : CantorBoundary) :
    (CantorStoneUltrafilter.principal x).toBoundary = x :=
  CantorStoneUltrafilter.toBoundary_principal x

/-- The selected atom of a Cantor Stone ultrafilter is exactly its recovered prefix. -/
theorem cantor_atom_mem_iff_prefix_eq
    (U : CantorStoneUltrafilter) (n : ℕ) (w : BitWord n) :
    atomCylinder n w ∈ U.filter ↔ boundaryPrefix n U.toBoundary = w :=
  CantorStoneUltrafilter.atom_mem_iff_prefix_eq U n w

end InfoGeometry.Canonical.StoneDualityBooleanEval


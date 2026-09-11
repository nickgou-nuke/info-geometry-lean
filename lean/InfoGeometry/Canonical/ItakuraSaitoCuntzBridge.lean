import InfoGeometry.Algebra.CuntzFibonacciBraidInclusion
import InfoGeometry.Algebra.FiniteSpinAlgebra

open CuntzFibonacciBraidInclusion

/-!
# Itakura--Saito ↔ Cuntz/Fibonacci Bridge — Re-export File

This file re-exports the operator-bridge lemmas proved in
`InfoGeometry.Algebra.CuntzFibonacciBraidInclusion` so downstream code can
import them from the canonical bridge namespace.

Re-exported:
* `ItakuraCuntzSocket`
* `divergenceSocket`
* `trace_conj_matrixToCuntz`
* `log_potential_preserved`
* `inv_pairing_conj_preserved`
* `itakuraSaito_invariance_under_conjugation`
-/

namespace InfoGeometry.Canonical.ItakuraSaitoCuntzBridge

/-!
### Closure debt

The following operator-bridge theorems are **not** proved yet:

* `cuntz_curvature_is_second_chern_form`: needs a genuine second-Chern-form
  readback `Tr(F ∧ F*)` on `CuntzAlg n`;
* `matrixToCuntz_itakura_equiv_of_comm`: needs explicit trace/inv/commutation
  bridge through the Cuntz generators for the supplied group element;
* `braid_flow_itakura_noncomm`: needs a verified nondegeneracy hypothesis for
  the Itakura--Saito divergence, not merely an assumed implication;
* direct finiteness/excision of `fibonacciBraidCuntzRepresentation`.

These remain debt labels until the algebra/socket owners supply exact data.
-/

end InfoGeometry.Canonical.ItakuraSaitoCuntzBridge

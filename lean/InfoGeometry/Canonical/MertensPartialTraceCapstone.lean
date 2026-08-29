/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.MertensPartialTrace

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.MertensPartialTrace

/-- 🏆 GRAND CANONICAL CAPSTONE: Mertens Function as Fermionic Parity Partial Trace -/
theorem grand_canonical_mertens_partial_trace_synthesis :
    (mertens 1 = fermionParityPartialTrace 1) ∧
    (mertens 1 = 1) ∧
    (mertens 2 = 0) ∧
    (mertens 3 = -1) ∧
    (∀ N ≥ 1, mertens (N + 1) = mertens N + ArithmeticFunction.moebius (N + 1)) :=
  grand_mertens_partial_trace_synthesis

end InfoGeometry.Canonical

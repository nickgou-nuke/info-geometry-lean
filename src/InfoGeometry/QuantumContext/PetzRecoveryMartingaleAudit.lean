/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MarkovGroupInversePetzCorner

/-!
# Kernel audit for algebraic full-matrix support compression

The generic ring identities are checked alongside their Markov range-projector
instantiations on the full matrix carrier. This audit makes no probability,
modular-cocycle, or subfactor-index claim.
-/

namespace InfoGeometry.QuantumContext.PetzMartingale.Audit

#check @InfoGeometry.QuantumContext.PetzMartingale.petz_recovery_idempotent
#check @InfoGeometry.QuantumContext.markovRange_petzRecovery_idempotent
#check @InfoGeometry.QuantumContext.markovRange_petzRecovery_range_iff_corner
#check @InfoGeometry.QuantumContext.markovRange_petzRecovery_corner_bimodule

#print axioms InfoGeometry.QuantumContext.PetzMartingale.petz_recovery_idempotent
#print axioms InfoGeometry.QuantumContext.markovRange_petzRecovery_idempotent
#print axioms InfoGeometry.QuantumContext.markovRange_petzRecovery_range_iff_corner
#print axioms InfoGeometry.QuantumContext.markovRange_petzRecovery_corner_bimodule

end InfoGeometry.QuantumContext.PetzMartingale.Audit

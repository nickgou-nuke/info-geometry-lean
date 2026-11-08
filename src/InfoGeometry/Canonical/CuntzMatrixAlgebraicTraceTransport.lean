/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.CuntzMatrixRingModuleComparisonBridge
import InfoGeometry.QuantumContext.MatrixStageFullColimitEquivalence

/-!
# Trace transport across the two full-matrix colimit presentations

This module records a concrete comparison theorem for the two already existing
algebraic presentations of the full matrix tower.  The quotient presentation
uses `MatrixStageLimit` and `limitTrace`; the categorical/direct-limit
presentation uses `Carrier` and `traceFunctional`.  The existing star-algebra
comparison identifies their finite-stage injections.  The main theorem below
proves that the normalized trace readouts agree on every quotient representative
by direct-limit induction.

No topological completion, positivity assertion, or physical interpretation is
introduced here.  The theorem is a compatibility result between two existing
algebraic carriers.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceTransport

open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Canonical.BitWordComplexCStarTowerNaturalityBridge
open InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
open InfoGeometry.QuantumContext.MatrixStageFullColimitEquivalence
open InfoGeometry.Canonical.CuntzMatrixRingModuleComparisonBridge

/--
The normalized trace on the quotient full-matrix colimit agrees with the
algebraic direct-limit trace after transport along the existing star-algebra
comparison.
-/
theorem limitTrace_carrierToQuotient_eq_traceFunctional
    (x : Carrier) :
    limitTrace (carrierToQuotient x) = traceFunctional x := by
  induction x using DirectLimit.induction with
  | _ n A =>
      change limitTrace (carrierToQuotient (stageInjection n A)) =
        traceFunctional (stageInjection n A)
      rw [carrierToQuotient_stage, canonicalStageHom_apply,
        limitTrace_toLimit, traceFunctional_stage]
      simpa using
        (stageStarAlgEquiv_normalizedTrace n
          ((stageStarAlgEquiv n).symm A))

/--
On a finite stage, the transported quotient trace is exactly the normalized
finite-stage matrix trace.
-/
theorem limitTrace_carrierToQuotient_stage
    (n : ℕ) (A : MatrixStage n) :
    limitTrace (carrierToQuotient (stageInjection n A)) =
      matrixTraceState n A := by
  rw [limitTrace_carrierToQuotient_eq_traceFunctional,
    traceFunctional_stage]

end InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceTransport

#print axioms InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceTransport.limitTrace_carrierToQuotient_eq_traceFunctional
#print axioms InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceTransport.limitTrace_carrierToQuotient_stage

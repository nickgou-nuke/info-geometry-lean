/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentChartDifferential
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChartSignCounterexample
import InfoGeometry.Canonical.StreamVIDeclarationAudit

/-!
# Native dependency order for idempotent chart and resolvent calculus

Reuse the checked type/value audit and finite reachability-order constructor.
Every declaration owned by the four mathematical extension modules is a
seed, including private/generated declarations. The complete project-owned
dependency closure and transitive axioms are inspected. The generated
`declarationPartialOrder` is precisely reachability in those actual edges;
the independent idempotency and analytic branches are not forced into a chain.

The kernel graph certificate, environment inspection, and external source
freshness remain separate validation obligations, as in the shared audit.
-/

open Lean Elab Command

namespace InfoGeometry.Canonical.IdempotentChartDeclarationAudit

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
run_cmd do
  InfoGeometry.Canonical.StreamVIDeclarationAudit.auditOwners
    #[`InfoGeometry.OperatorAlgebra.ResolventChartDifferential,
      `InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentChartResolvent,
      `InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentChartDifferential,
      `InfoGeometry.OperatorAlgebra.PeirceSpine.ChartSignCounterexample]
    #[] #[]

end InfoGeometry.Canonical.IdempotentChartDeclarationAudit

def AuditResult.toMetric (a : AuditResult) : MathfulnessMetric :=
  { termNodeCount := a.termNodeCount
    usesNontrivialGlobalProofConst := a.hasNontrivialConst
    containsVacuousSockets := a.containsVacuousSockets }
structure AuditResult where
  nodeCount : Nat
  nontrivialConsts : List Name
  trivialConsts : List Name
  projections : Nat
  localHypothesisOnly : Bool
  unfoldedWrappers : List Name
deriving Repr
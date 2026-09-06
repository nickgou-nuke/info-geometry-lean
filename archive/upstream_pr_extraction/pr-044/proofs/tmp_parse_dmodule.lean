import proofs.NonIsoConf3DModuleRankAudit

#eval do
  let txt := "{\"source\": \"non_iso_conf3_rank32_external_audit.py\", \"D\": 4, \"ambient_dimension\": 8, \"status\": \"inconclusive\", \"toolchain\": {\"singular\": \"missing\", \"macaulay2\": \"missing\", \"sage\": \"missing\", \"sagemanifolds\": \"missing\"}, \"pointwise\": {\"betti\": [], \"total_rank\": 0, \"max_degree\": 0}, \"three_quadric_codim_data\": {\"codimQA\": 1, \"codimQB\": 1, \"codimQAB\": 1, \"codimQA_QB\": 2, \"codimQA_QAB\": 2, \"codimQB_QAB\": 2, \"codimTriple\": 3}, \"rank_decision_verifications\": {\"resolvedDupontArrangementConstructed\": false, \"betaGysinLeavesTwoIndependentFluxClasses\": false, \"dupontModelComputesActualDeRham\": false, \"cooperadFunctorialityForResolvedModel\": false, \"codimDataEqExpected\": true}, \"notes\": null }"
  match NonIsoConf3DModuleRankAudit.parseReportFromString txt with
  | none => IO.println "none"
  | some r => do
      IO.println s!"toolchain.sage={r.toolchain.sage}"
      IO.println s!"toolchain.sagemanifolds={r.toolchain.sagemanifolds}"

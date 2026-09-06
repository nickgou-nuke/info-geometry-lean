import Mathlib
import Lean
import proofs.NonIsoConf3DeRhamCooperad
import proofs.NonIsoConf3RankDecision

noncomputable section

namespace NonIsoConf3DModuleRankAudit

open NonIsoConf3RankDecision
open NonIsoConf3DeRhamCooperad

structure ToolchainReport where
  singular : String
  macaulay2 : String
  sage : String
  sagemanifolds : Option String
  deriving Repr, Lean.FromJson

structure BettiPointwiseReport where
  betti : List ℕ
  total_rank : ℕ
  max_degree : ℕ
  deriving Repr, Lean.FromJson

structure ThreeQuadricCodimReport where
  codimQA : ℕ
  codimQB : ℕ
  codimQAB : ℕ
  codimQA_QB : ℕ
  codimQA_QAB : ℕ
  codimQB_QAB : ℕ
  codimTriple : ℕ
  deriving Repr, Lean.FromJson

structure ReportVerification where
  resolvedDupontArrangementConstructed : Bool
  betaGysinLeavesTwoIndependentFluxClasses : Bool
  dupontModelComputesActualDeRham : Bool
  cooperadFunctorialityForResolvedModel : Bool
  codimDataEqExpected : Bool
  deriving Repr, Lean.FromJson

structure InputPaths where
  singular : String
  macaulay2 : String
  deriving Repr, Lean.FromJson

structure ExternalDModuleAuditReport where
  source : String
  D : ℕ
  ambient_dimension : ℕ
  status : String
  toolchain : ToolchainReport
  pointwise : BettiPointwiseReport
  three_quadric_codim_data : ThreeQuadricCodimReport
  rank_decision_verifications : ReportVerification
  notes : Option String
  inputs : Option InputPaths
  deriving Repr, Lean.FromJson

def ThreeQuadricCodimReport.toModelData (C : ThreeQuadricCodimReport) : ThreeQuadricCodimData where
  codimQA := C.codimQA
  codimQB := C.codimQB
  codimQAB := C.codimQAB
  codimQA_QB := C.codimQA_QB
  codimQA_QAB := C.codimQA_QAB
  codimQB_QAB := C.codimQB_QAB
  codimTriple := C.codimTriple

def ExternalDModuleAuditReport.pointwiseTotal (R : ExternalDModuleAuditReport) : ℕ :=
  R.pointwise.total_rank

def ExternalDModuleAuditReport.pointwiseBettiSum (R : ExternalDModuleAuditReport) : ℕ :=
  R.pointwise.betti.sum

def ExternalDModuleAuditReport.bettiSumMatchesReported (R : ExternalDModuleAuditReport) : Prop :=
  R.pointwiseBettiSum = R.pointwiseTotal

def ExternalDModuleAuditReport.codimDataEqExpected (R : ExternalDModuleAuditReport) : Prop :=
  R.three_quadric_codim_data.toModelData = expectedCodimData

def ExternalDModuleAuditReport.isVerified (R : ExternalDModuleAuditReport) : Prop :=
  R.status = "verified"

def parseReportFromString (txt : String) : Option ExternalDModuleAuditReport :=
  match Lean.Json.parse txt with
  | .ok j =>
      match Lean.FromJson.fromJson? j with
      | .ok r => some r
      | .error _ => none
  | .error _ => none

def parseReportFromFile (path : String) : IO (Option ExternalDModuleAuditReport) := do
  try
    let txt ← IO.FS.readFile ⟨path⟩
    return parseReportFromString txt
  catch _ =>
    return none

theorem codim_report_expected_fields (C : ThreeQuadricCodimReport)
    (h : C.toModelData = expectedCodimData) :
    C.codimQA = 1 ∧
    C.codimQB = 1 ∧
    C.codimQAB = 1 ∧
    C.codimQA_QB = 2 ∧
    C.codimQA_QAB = 2 ∧
    C.codimQB_QAB = 2 ∧
    C.codimTriple = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
      simpa [ThreeQuadricCodimReport.toModelData, expectedCodimData]
        using congrArg ThreeQuadricCodimData.codimQA h
  ·
      simpa [ThreeQuadricCodimReport.toModelData, expectedCodimData]
        using congrArg ThreeQuadricCodimData.codimQB h
  ·
      simpa [ThreeQuadricCodimReport.toModelData, expectedCodimData]
        using congrArg ThreeQuadricCodimData.codimQAB h
  ·
      simpa [ThreeQuadricCodimReport.toModelData, expectedCodimData]
        using congrArg ThreeQuadricCodimData.codimQA_QB h
  ·
      simpa [ThreeQuadricCodimReport.toModelData, expectedCodimData]
        using congrArg ThreeQuadricCodimData.codimQA_QAB h
  ·
      simpa [ThreeQuadricCodimReport.toModelData, expectedCodimData]
        using congrArg ThreeQuadricCodimData.codimQB_QAB h
  ·
      simpa [ThreeQuadricCodimReport.toModelData, expectedCodimData]
        using congrArg ThreeQuadricCodimData.codimTriple h

theorem report_codim_not_triple_dependent (R : ExternalDModuleAuditReport)
    (hCodim : R.codimDataEqExpected) :
    ¬ tripleDependent R.three_quadric_codim_data.toModelData := by
  intro hDependent
  unfold ExternalDModuleAuditReport.codimDataEqExpected at hCodim
  rw [hCodim] at hDependent
  exact expected_triple_not_dependent hDependent

theorem rank32_decision_from_report_codim
    (R : ExternalDModuleAuditReport)
    (hCodim : R.codimDataEqExpected) :
    (¬ tripleDependent R.three_quadric_codim_data.toModelData) ∧
    Fintype.card ProductBasis = 32 ∧
    Fintype.card OSFluxBasis = 24 ∧
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 := by
  rcases rank32_decision_from_dupont_independence with
    ⟨_hExpectedCodim, hProduct, hOS, hGap⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using report_codim_not_triple_dependent R hCodim
  · simpa using hProduct
  · simpa using hOS
  · simpa using hGap

theorem pointwise_betti_sum_eq_rank32
    (R : ExternalDModuleAuditReport)
    (hTotal : R.pointwiseTotal = 32)
    (hSum : R.bettiSumMatchesReported) :
    R.pointwiseBettiSum = 32 := by
  calc
    R.pointwiseBettiSum = R.pointwiseTotal := hSum
    _ = 32 := hTotal

theorem verified_report_rank32_decision
    (R : ExternalDModuleAuditReport)
    (hStatus : R.isVerified)
    (hCodim : R.codimDataEqExpected)
    (hTotal : R.pointwiseTotal = 32)
    (hSum : R.bettiSumMatchesReported) :
    R.status = "verified" ∧
    R.pointwiseBettiSum = 32 ∧
    ¬ tripleDependent R.three_quadric_codim_data.toModelData ∧
    Fintype.card ProductBasis = 32 ∧
    Fintype.card OSFluxBasis = 24 ∧
    Fintype.card ProductBasis - Fintype.card OSFluxBasis = 8 := by
  rcases rank32_decision_from_report_codim R hCodim with
    ⟨hIndependent, hProduct, hOS, hGap⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ExternalDModuleAuditReport.isVerified] using hStatus
  · simpa using pointwise_betti_sum_eq_rank32 R hTotal hSum
  · simpa using hIndependent
  · simpa using hProduct
  · simpa using hOS
  · simpa using hGap

end NonIsoConf3DModuleRankAudit

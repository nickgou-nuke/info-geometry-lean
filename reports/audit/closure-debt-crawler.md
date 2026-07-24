# Lean Closure Debt Crawler Report

Generated: `2026-07-24T20:59:25.114463+00:00`
Root: `lean`
Authority tier: `heuristic-proxy`

## Summary

- Files scanned: **50**
- Findings: **333**
- Hard: **4**
- Soft: **167**
- Advisory: **162**
- File status counts: clean=33, advisory=14, open_gap=3

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/Agent.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/Agent/CompilerBridgeCore.lean` | `advisory` | 16 | 0 | 8 | 0 | 8 |
| `lean/Agent/ProofServerRpc.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/Agent/ProofStateExport.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/Agent/Protocol.lean` | `advisory` | 136 | 0 | 68 | 0 | 68 |
| `lean/AuditNative.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/AuditStrict.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/AFPGaussJordan.lean` | `advisory` | 23 | 0 | 0 | 23 | 23 |
| `lean/DAG/AffineProjectiveClosure.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/AlgebraicExponential.lean` | `advisory` | 19 | 0 | 8 | 3 | 11 |
| `lean/DAG/Algo/All.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/Algo/Check.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/Algo/Core.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/Algo/Smoke.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/Algo/Traversal.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/Analysis.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/AnalyticBridge.lean` | `advisory` | 23 | 0 | 11 | 1 | 12 |
| `lean/DAG/Basic.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/Betti.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/BlockDecomposition.lean` | `advisory` | 8 | 0 | 4 | 0 | 4 |
| `lean/DAG/BlockExport.lean` | `open_gap` | 10 | 2 | 0 | 0 | 2 |
| `lean/DAG/CategoryBridge.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/CategoryBridgeTest.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/CategoryQuiver.lean` | `advisory` | 24 | 0 | 12 | 0 | 12 |
| `lean/DAG/ChiralDiracAnticommutation.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/CocycleBridge.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/CocycleBridgeActivation.lean` | `advisory` | 8 | 0 | 4 | 0 | 4 |
| `lean/DAG/ConeCommand.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/ConnesHodgeBridge.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/DeclIndex.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/DiracLaplacian.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/Disassembler.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/DisconnectedAudit.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/DisconnectedCapstoneAudit.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/Dominators.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/EckmannHodge.lean` | `advisory` | 72 | 0 | 4 | 64 | 68 |
| `lean/DAG/ExactMorphism.lean` | `advisory` | 8 | 0 | 4 | 0 | 4 |
| `lean/DAG/ExactMorphismTest.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/ExactProoflessnessAudit.lean` | `open_gap` | 5 | 1 | 0 | 0 | 1 |
| `lean/DAG/ExportDecls.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/ExportForwardGraph.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/ExprArangoExport.lean` | `open_gap` | 41 | 1 | 18 | 0 | 19 |
| `lean/DAG/ExprFingerprint.lean` | `advisory` | 6 | 0 | 3 | 0 | 3 |
| `lean/DAG/FinalSearch.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/FindFinrank.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/FunctionalGaussJordan.lean` | `advisory` | 18 | 0 | 3 | 12 | 15 |
| `lean/DAG/Functor.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |
| `lean/DAG/GaussianElimination.lean` | `advisory` | 81 | 0 | 11 | 59 | 70 |
| `lean/DAG/GeneralizedTwoComplex.lean` | `advisory` | 18 | 0 | 9 | 0 | 9 |
| `lean/DAG/GlobalDisassembler.lean` | `clean` | 0 | 0 | 0 | 0 | 0 |

## Findings by file

### `lean/Agent.lean`
- module: `Agent`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/Agent/CompilerBridgeCore.lean`
- module: `Agent.CompilerBridgeCore`
- status: `advisory`
- debt_score: `16`
- findings:
  - L21 [soft] `law-field-locker` in `structure-field ProofStateView.diagnostics` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L21 [soft] `uninstantiated-law-locker` in `structure ProofStateView` — structure/class has theorem-like fields but no visible constructor site (`.mk`, `: Name :=`, or `: Name where`) in the scanned root; this may be a proof-debt locker rather than implemented mathematics
  - L22 [soft] `law-field-locker` in `structure-field ProofStateView.goals` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L238 [soft] `law-field-locker` in `structure-field HeadMeta.head` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L238 [soft] `uninstantiated-law-locker` in `structure HeadMeta` — structure/class has theorem-like fields but no visible constructor site (`.mk`, `: Name :=`, or `: Name where`) in the scanned root; this may be a proof-debt locker rather than implemented mathematics
  - L239 [soft] `law-field-locker` in `structure-field HeadMeta.source` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L240 [soft] `law-field-locker` in `structure-field HeadMeta.fingerprint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L241 [soft] `law-field-locker` in `structure-field HeadMeta.exprFingerprint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

### `lean/Agent/ProofServerRpc.lean`
- module: `Agent.ProofServerRpc`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/Agent/ProofStateExport.lean`
- module: `Agent.ProofStateExport`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/Agent/Protocol.lean`
- module: `Agent.Protocol`
- status: `advisory`
- debt_score: `136`
- findings:
  - L72 [soft] `law-field-locker` in `structure-field ExprFingerprintView.exprKind` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `uninstantiated-law-locker` in `structure ExprFingerprintView` — structure/class has theorem-like fields but no visible constructor site (`.mk`, `: Name :=`, or `: Name where`) in the scanned root; this may be a proof-debt locker rather than implemented mathematics
  - L73 [soft] `law-field-locker` in `structure-field ExprFingerprintView.semanticHead` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field ExprFingerprintView.binderDepth` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L75 [soft] `law-field-locker` in `structure-field ExprFingerprintView.appArity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L76 [soft] `law-field-locker` in `structure-field ExprFingerprintView.argHeadFingerprints` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L77 [soft] `law-field-locker` in `structure-field ExprFingerprintView.fingerprintV1` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L78 [soft] `law-field-locker` in `structure-field ExprFingerprintView.fingerprintSource` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L102 [soft] `law-field-locker` in `structure-field CompilerError.classificationProvenance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L103 [soft] `law-field-locker` in `structure-field CompilerError.file` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L104 [soft] `law-field-locker` in `structure-field CompilerError.line` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L106 [soft] `law-field-locker` in `structure-field CompilerError.column` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L113 [soft] `law-field-locker` in `structure-field LocalDeclView.binderKind` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L113 [soft] `uninstantiated-law-locker` in `structure LocalDeclView` — structure/class has theorem-like fields but no visible constructor site (`.mk`, `: Name :=`, or `: Name where`) in the scanned root; this may be a proof-debt locker rather than implemented mathematics
  - L115 [soft] `law-field-locker` in `structure-field LocalDeclView.typeHead` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L116 [soft] `law-field-locker` in `structure-field LocalDeclView.typeHeadSource` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L117 [soft] `law-field-locker` in `structure-field LocalDeclView.typeHeadFingerprint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L118 [soft] `law-field-locker` in `structure-field LocalDeclView.typeExprFingerprint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L119 [soft] `law-field-locker` in `structure-field LocalDeclView.value` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L120 [soft] `law-field-locker` in `structure-field LocalDeclView.isLet` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L121 [soft] `law-field-locker` in `structure-field LocalDeclView.isInstance` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L122 [soft] `law-field-locker` in `structure-field LocalDeclView.isImplementationDetail` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L130 [soft] `law-field-locker` in `structure-field GoalView.targetHead` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L130 [soft] `uninstantiated-law-locker` in `structure GoalView` — structure/class has theorem-like fields but no visible constructor site (`.mk`, `: Name :=`, or `: Name where`) in the scanned root; this may be a proof-debt locker rather than implemented mathematics
  - L131 [soft] `law-field-locker` in `structure-field GoalView.targetHeadSource` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L132 [soft] `law-field-locker` in `structure-field GoalView.targetHeadFingerprint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L133 [soft] `law-field-locker` in `structure-field GoalView.targetExprFingerprint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L142 [soft] `law-field-locker` in `structure-field GetProofStateParams.version` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L143 [soft] `law-field-locker` in `structure-field GetProofStateParams.posLine` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L144 [soft] `law-field-locker` in `structure-field GetProofStateParams.posCharacter` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L150 [soft] `law-field-locker` in `structure-field GetProofStateResult.diagnostics` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L151 [soft] `law-field-locker` in `structure-field GetProofStateResult.goals` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L155 [soft] `law-field-locker` in `structure-field GetGoalTargetsParams.version` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L155 [soft] `uninstantiated-law-locker` in `structure GetGoalTargetsParams` — structure/class has theorem-like fields but no visible constructor site (`.mk`, `: Name :=`, or `: Name where`) in the scanned root; this may be a proof-debt locker rather than implemented mathematics
  - L156 [soft] `law-field-locker` in `structure-field GetGoalTargetsParams.posLine` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L157 [soft] `law-field-locker` in `structure-field GetGoalTargetsParams.posCharacter` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L163 [soft] `law-field-locker` in `structure-field GetGoalTargetsResult.diagnostics` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L164 [soft] `law-field-locker` in `structure-field GetGoalTargetsResult.goals` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L165 [soft] `law-field-locker` in `structure-field GetGoalTargetsResult.goalCount` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L169 [soft] `law-field-locker` in `structure-field GetEnvFingerprintParams.version` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L169 [soft] `uninstantiated-law-locker` in `structure GetEnvFingerprintParams` — structure/class has theorem-like fields but no visible constructor site (`.mk`, `: Name :=`, or `: Name where`) in the scanned root; this may be a proof-debt locker rather than implemented mathematics
  - L175 [soft] `law-field-locker` in `structure-field GetEnvFingerprintResult.diagnostics` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L179 [soft] `law-field-locker` in `structure-field CheckSnippetParams.version` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L180 [soft] `law-field-locker` in `structure-field CheckSnippetParams.posLine` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L181 [soft] `law-field-locker` in `structure-field CheckSnippetParams.posCharacter` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L187 [soft] `law-field-locker` in `structure-field CheckSnippetResult.diagnostics` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L188 [soft] `law-field-locker` in `structure-field CheckSnippetResult.goals` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L189 [soft] `law-field-locker` in `structure-field CheckSnippetResult.goalCount` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L193 [soft] `law-field-locker` in `structure-field ValidateDeclParams.version` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L195 [soft] `law-field-locker` in `structure-field ValidateDeclParams.posLine` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L196 [soft] `law-field-locker` in `structure-field ValidateDeclParams.posCharacter` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L197 [soft] `law-field-locker` in `structure-field ValidateDeclParams.prettyPrintType` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L198 [soft] `law-field-locker` in `structure-field ValidateDeclParams.prettyPrintValue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L202 [soft] `law-field-locker` in `structure-field GetDeclValueParams.version` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L204 [soft] `law-field-locker` in `structure-field GetDeclValueParams.posLine` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L205 [soft] `law-field-locker` in `structure-field GetDeclValueParams.posCharacter` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L211 [soft] `law-field-locker` in `structure-field GetDeclValueResult.diagnostics` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L212 [soft] `law-field-locker` in `structure-field GetDeclValueResult.declFound` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L213 [soft] `law-field-locker` in `structure-field GetDeclValueResult.declarationValue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L219 [soft] `law-field-locker` in `structure-field ValidateDeclResult.diagnostics` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L220 [soft] `law-field-locker` in `structure-field ValidateDeclResult.declFound` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L221 [soft] `law-field-locker` in `structure-field ValidateDeclResult.theoremType` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L222 [soft] `law-field-locker` in `structure-field ValidateDeclResult.theoremTypeHead` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L223 [soft] `law-field-locker` in `structure-field ValidateDeclResult.theoremTypeHeadSource` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L224 [soft] `law-field-locker` in `structure-field ValidateDeclResult.theoremTypeHeadFingerprint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L225 [soft] `law-field-locker` in `structure-field ValidateDeclResult.theoremTypeExprFingerprint` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L226 [soft] `law-field-locker` in `structure-field ValidateDeclResult.declarationValue` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L227 [soft] `law-field-locker` in `structure-field ValidateDeclResult.hasSorry` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

### `lean/AuditNative.lean`
- module: `AuditNative`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/AuditStrict.lean`
- module: `AuditStrict`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/AFPGaussJordan.lean`
- module: `DAG.AFPGaussJordan`
- status: `advisory`
- debt_score: `23`
- findings:
  - L23 [advisory] `existential-packaging` in `def PivotFun` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L39 [advisory] `local-hypothesis-injection` in `lemma non_pivot_rows_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L40 [advisory] `local-hypothesis-injection` in `lemma non_pivot_rows_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L93 [advisory] `local-hypothesis-injection` in `lemma rank_transpose_le_pivot_card` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L129 [advisory] `local-hypothesis-injection` in `lemma rank_transpose_le_pivot_card` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L136 [advisory] `local-hypothesis-injection` in `lemma rank_transpose_le_pivot_card` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L159 [advisory] `local-hypothesis-injection` in `lemma rank_transpose_le_pivot_card` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L170 [advisory] `local-hypothesis-injection` in `lemma pivot_card_le_rank` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L175 [advisory] `local-hypothesis-injection` in `lemma pivot_card_le_rank` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L184 [advisory] `local-hypothesis-injection` in `lemma pivot_card_le_rank` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L202 [advisory] `local-hypothesis-injection` in `lemma pivot_card_le_rank` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L211 [advisory] `local-hypothesis-injection` in `lemma pivot_card_le_rank` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L214 [advisory] `local-hypothesis-injection` in `lemma pivot_card_le_rank` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L215 [advisory] `local-hypothesis-injection` in `lemma pivot_card_le_rank` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L234 [advisory] `local-hypothesis-injection` in `lemma pivot_card_le_rank` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L237 [advisory] `local-hypothesis-injection` in `lemma pivot_card_le_rank` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L239 [advisory] `local-hypothesis-injection` in `lemma pivot_card_le_rank` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L256 [advisory] `local-hypothesis-injection` in `lemma pivotRows_card_eq_nat_filter` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L261 [advisory] `local-hypothesis-injection` in `lemma pivotRows_card_eq_nat_filter` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L269 [advisory] `local-hypothesis-injection` in `lemma pivotRows_card_eq_nat_filter` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L273 [advisory] `local-hypothesis-injection` in `lemma pivotRows_card_eq_nat_filter` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L276 [advisory] `local-hypothesis-injection` in `lemma pivotRows_card_eq_nat_filter` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L292 [advisory] `local-hypothesis-injection` in `theorem rank_rref_eq_pivot_count` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

### `lean/DAG/AffineProjectiveClosure.lean`
- module: `DAG.AffineProjectiveClosure`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/AlgebraicExponential.lean`
- module: `DAG.AlgebraicExponential`
- status: `advisory`
- debt_score: `19`
- findings:
  - L30 [soft] `simp-law-injection` in `simp-declaration algebraicExp_eq_one_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L32 [soft] `skeletal-proof` in `theorem algebraicExp_eq_one_add` — proof appears to close via minimal tactic one-liner
  - L35 [soft] `simp-law-injection` in `simp-declaration algebraicExp_neg_eq_one_sub` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L42 [soft] `skeletal-proof` in `theorem algebraicExp_mul_neg` — proof appears to close via minimal tactic one-liner
  - L48 [soft] `skeletal-proof` in `theorem algebraicExp_neg_mul` — proof appears to close via minimal tactic one-liner
  - L54 [soft] `skeletal-proof` in `theorem algebraicExp_unit_eq_tessellationUnit` — proof appears to close via minimal tactic one-liner
  - L73 [soft] `simp-law-injection` in `simp-declaration timedNilpotentExp_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L75 [soft] `skeletal-proof` in `theorem timedNilpotentExp_zero` — proof appears to close via minimal tactic one-liner
  - L89 [advisory] `local-hypothesis-injection` in `theorem timedNilpotentExp_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L102 [advisory] `local-hypothesis-injection` in `theorem timedNilpotentExp_mul_neg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L115 [advisory] `local-hypothesis-injection` in `theorem timedNilpotentExp_neg_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

### `lean/DAG/Algo/All.lean`
- module: `DAG.Algo.All`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/Algo/Check.lean`
- module: `DAG.Algo.Check`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/Algo/Core.lean`
- module: `DAG.Algo.Core`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/Algo/Smoke.lean`
- module: `DAG.Algo.Smoke`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/Algo/Traversal.lean`
- module: `DAG.Algo.Traversal`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/Analysis.lean`
- module: `DAG.Analysis`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/AnalyticBridge.lean`
- module: `DAG.AnalyticBridge`
- status: `advisory`
- debt_score: `23`
- findings:
  - L29 [soft] `simp-law-injection` in `simp-declaration uhfOf_map` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L38 [soft] `simp-law-injection` in `simp-declaration finiteFlow_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L40 [soft] `skeletal-proof` in `theorem finiteFlow_apply` — proof appears to close via minimal tactic one-liner
  - L43 [soft] `simp-law-injection` in `simp-declaration flow_commutes_with_splitCliffordMap` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L45 [soft] `skeletal-proof` in `theorem flow_commutes_with_splitCliffordMap` — proof appears to close via minimal tactic one-liner
  - L54 [soft] `simp-law-injection` in `simp-declaration uhfModularFlow_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L56 [soft] `skeletal-proof` in `theorem uhfModularFlow_apply` — proof appears to close via minimal tactic one-liner
  - L59 [soft] `simp-law-injection` in `simp-declaration uhfModularFlow_stage` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L61 [soft] `skeletal-proof` in `theorem uhfModularFlow_stage` — proof appears to close via minimal tactic one-liner
  - L64 [soft] `simp-law-injection` in `simp-declaration uhfModularFlow_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L66 [soft] `skeletal-proof` in `theorem uhfModularFlow_add` — proof appears to close via minimal tactic one-liner
  - L69 [advisory] `existential-packaging` in `theorem analytic_completion_has_nilpotent_lift` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

### `lean/DAG/Basic.lean`
- module: `DAG.Basic`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/Betti.lean`
- module: `DAG.Betti`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/BlockDecomposition.lean`
- module: `DAG.BlockDecomposition`
- status: `advisory`
- debt_score: `8`
- findings:
  - L112 [soft] `simp-law-injection` in `simp-declaration dimensionsOf_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L117 [soft] `simp-law-injection` in `simp-declaration diracOf_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L121 [soft] `simp-law-injection` in `simp-declaration chiralOf_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L125 [soft] `simp-law-injection` in `simp-declaration laplacianOf_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

### `lean/DAG/BlockExport.lean`
- module: `DAG.BlockExport`
- status: `open_gap`
- debt_score: `10`
- findings:
  - L247 [hard] `partial-bypass` in `declaration <partial>` — partial declaration bypasses Lean termination/productivity checking
  - L366 [hard] `partial-bypass` in `declaration <partial>` — partial declaration bypasses Lean termination/productivity checking

### `lean/DAG/CategoryBridge.lean`
- module: `DAG.CategoryBridge`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/CategoryBridgeTest.lean`
- module: `DAG.CategoryBridgeTest`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/CategoryQuiver.lean`
- module: `DAG.CategoryQuiver`
- status: `advisory`
- debt_score: `24`
- findings:
  - L16 [soft] `law-field-locker` in `structure-field CategoryQuiverMorphism.domOK` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L17 [soft] `law-field-locker` in `structure-field CategoryQuiverMorphism.codOK` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L52 [soft] `law-field-locker` in `structure-field VerifiedCategoryData.id` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field VerifiedCategoryData.comp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L54 [soft] `law-field-locker` in `structure-field VerifiedCategoryData.id_comp` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L55 [soft] `law-field-locker` in `structure-field VerifiedCategoryData.comp_id` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field VerifiedCategoryData.assoc` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L70 [soft] `law-field-locker` in `structure-field HarvestWitnesses.idWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L71 [soft] `law-field-locker` in `structure-field HarvestWitnesses.compWitness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field HarvestWitnesses.id_comp_witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L73 [soft] `law-field-locker` in `structure-field HarvestWitnesses.comp_id_witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `law-field-locker` in `structure-field HarvestWitnesses.assoc_witness` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

### `lean/DAG/ChiralDiracAnticommutation.lean`
- module: `DAG.ChiralDiracAnticommutation`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/CocycleBridge.lean`
- module: `DAG.CocycleBridge`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/CocycleBridgeActivation.lean`
- module: `DAG.CocycleBridgeActivation`
- status: `advisory`
- debt_score: `8`
- findings:
  - L51 [soft] `law-field-locker` in `structure-field CocycleBridge.analyticBridge` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L53 [soft] `law-field-locker` in `structure-field CocycleBridge.connesCocycle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field CocycleBridge.hexagonCocycle` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field CocycleBridge.chain` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

### `lean/DAG/ConeCommand.lean`
- module: `DAG.ConeCommand`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/ConnesHodgeBridge.lean`
- module: `DAG.ConnesHodgeBridge`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/DeclIndex.lean`
- module: `DAG.DeclIndex`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/DiracLaplacian.lean`
- module: `DAG.DiracLaplacian`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/Disassembler.lean`
- module: `DAG.Disassembler`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/DisconnectedAudit.lean`
- module: `DAG.DisconnectedAudit`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/DisconnectedCapstoneAudit.lean`
- module: `DAG.DisconnectedCapstoneAudit`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/Dominators.lean`
- module: `DAG.Dominators`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/EckmannHodge.lean`
- module: `DAG.EckmannHodge`
- status: `advisory`
- debt_score: `72`
- findings:
  - L25 [advisory] `local-hypothesis-injection` in `lemma ker_mul_transpose_eq_ker_transpose` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L27 [advisory] `local-hypothesis-injection` in `lemma ker_mul_transpose_eq_ker_transpose` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L29 [advisory] `local-hypothesis-injection` in `lemma ker_mul_transpose_eq_ker_transpose` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L33 [advisory] `local-hypothesis-injection` in `lemma ker_mul_transpose_eq_ker_transpose` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L38 [advisory] `local-hypothesis-injection` in `lemma rank_mul_transpose_eq_rank` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L51 [advisory] `local-hypothesis-injection` in `lemma rank_mul_transpose_eq_rank` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L52 [advisory] `local-hypothesis-injection` in `lemma rank_mul_transpose_eq_rank` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L55 [advisory] `local-hypothesis-injection` in `lemma rank_mul_transpose_eq_rank` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L56 [advisory] `local-hypothesis-injection` in `lemma rank_mul_transpose_eq_rank` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L58 [soft] `skeletal-proof` in `lemma full_rank_trivial_kernel` — proof appears to close via minimal tactic one-liner
  - L66 [advisory] `local-hypothesis-injection` in `lemma full_rank_trivial_kernel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L69 [advisory] `local-hypothesis-injection` in `lemma full_rank_trivial_kernel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L70 [advisory] `local-hypothesis-injection` in `lemma full_rank_trivial_kernel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L72 [advisory] `local-hypothesis-injection` in `lemma full_rank_trivial_kernel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L85 [advisory] `local-hypothesis-injection` in `lemma ker_sq_eq_ker_psd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L86 [advisory] `local-hypothesis-injection` in `lemma ker_sq_eq_ker_psd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L88 [advisory] `local-hypothesis-injection` in `lemma ker_sq_eq_ker_psd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L92 [advisory] `local-hypothesis-injection` in `lemma ker_sq_eq_ker_psd` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L94 [soft] `skeletal-proof` in `lemma ker_sq_eq_ker_AAtranspose` — proof appears to close via minimal tactic one-liner
  - L100 [advisory] `local-hypothesis-injection` in `lemma ker_sq_eq_ker_AAtranspose` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L106 [advisory] `local-hypothesis-injection` in `lemma rank_sq_eq_rank_AAtranspose` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L126 [advisory] `local-hypothesis-injection` in `lemma im_sq_eq_im_AAtranspose` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L129 [advisory] `local-hypothesis-injection` in `lemma im_sq_eq_im_AAtranspose` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L134 [advisory] `local-hypothesis-injection` in `lemma im_sq_eq_im_AAtranspose` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L138 [soft] `skeletal-proof` in `lemma laplacian_rank_eq_sum` — proof appears to close via minimal tactic one-liner
  - L145 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L146 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L147 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L148 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L149 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L150 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L152 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L154 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L155 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L156 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L157 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L159 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L160 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L161 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L162 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L163 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L165 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L172 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L175 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L176 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L178 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L180 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L182 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L185 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L187 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L194 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L195 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L196 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L199 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L201 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L202 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L203 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L211 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L212 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L213 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L216 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L221 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L229 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L233 [advisory] `local-hypothesis-injection` in `lemma laplacian_rank_eq_sum` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L264 [advisory] `local-hypothesis-injection` in `theorem eckmann_discrete_hodge_matrix` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L283 [soft] `skeletal-proof` in `theorem eckmann_hodge_nullity` — proof appears to close via minimal tactic one-liner
  - L318 [advisory] `local-hypothesis-injection` in `theorem eckmann_hodge_nullity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L319 [advisory] `local-hypothesis-injection` in `theorem eckmann_hodge_nullity` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

### `lean/DAG/ExactMorphism.lean`
- module: `DAG.ExactMorphism`
- status: `advisory`
- debt_score: `8`
- findings:
  - L98 [soft] `law-field-locker` in `structure-field MorphismState.entries` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `law-field-locker` in `structure-field MorphismState.byDom` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L100 [soft] `law-field-locker` in `structure-field MorphismState.byCod` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L101 [soft] `law-field-locker` in `structure-field MorphismState.indexed` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

### `lean/DAG/ExactMorphismTest.lean`
- module: `DAG.ExactMorphismTest`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/ExactProoflessnessAudit.lean`
- module: `DAG.ExactProoflessnessAudit`
- status: `open_gap`
- debt_score: `5`
- findings:
  - L127 [hard] `partial-bypass` in `declaration <partial>` — partial declaration bypasses Lean termination/productivity checking

### `lean/DAG/ExportDecls.lean`
- module: `DAG.ExportDecls`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/ExportForwardGraph.lean`
- module: `DAG.ExportForwardGraph`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/ExprArangoExport.lean`
- module: `DAG.ExprArangoExport`
- status: `open_gap`
- debt_score: `41`
- findings:
  - L21 [soft] `law-field-locker` in `structure-field NodeRow.deBruijnHash` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L22 [soft] `law-field-locker` in `structure-field NodeRow.alphaLocalHash` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L23 [soft] `law-field-locker` in `structure-field NodeRow.shapeHash` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L24 [soft] `law-field-locker` in `structure-field NodeRow.quality` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L36 [soft] `law-field-locker` in `structure-field EdgeRow.incidenceHash` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `law-field-locker` in `structure-field EdgeRow.binderIncidenceHash` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [soft] `law-field-locker` in `structure-field EdgeRow.quality` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field EdgeRow.notes` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field ExportState.declKeyMap` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [soft] `law-field-locker` in `structure-field ExportState.nextExprNodeId` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L58 [soft] `law-field-locker` in `structure-field ExportState.nextEdgeId` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L59 [soft] `law-field-locker` in `structure-field ExportState.nodeCount` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field ExportState.edgeCount` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L61 [soft] `law-field-locker` in `structure-field ExportState.brokenBVarCount` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L62 [soft] `law-field-locker` in `structure-field ExportState.pendingDecls` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field ExportState.pendingDeclCursor` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field ExportState.enqueuedDecls` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [soft] `law-field-locker` in `structure-field ExportState.processedDecls` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L368 [hard] `partial-bypass` in `declaration <partial>` — partial declaration bypasses Lean termination/productivity checking

### `lean/DAG/ExprFingerprint.lean`
- module: `DAG.ExprFingerprint`
- status: `advisory`
- debt_score: `6`
- findings:
  - L32 [soft] `law-field-locker` in `structure-field ExprFingerprint.deBruijnIncidenceHash` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `uninstantiated-law-locker` in `structure ExprFingerprint` — structure/class has theorem-like fields but no visible constructor site (`.mk`, `: Name :=`, or `: Name where`) in the scanned root; this may be a proof-debt locker rather than implemented mathematics
  - L34 [soft] `law-field-locker` in `structure-field ExprFingerprint.alphaLocalHash` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

### `lean/DAG/FinalSearch.lean`
- module: `DAG.FinalSearch`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/FindFinrank.lean`
- module: `DAG.FindFinrank`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/FunctionalGaussJordan.lean`
- module: `DAG.FunctionalGaussJordan`
- status: `advisory`
- debt_score: `18`
- findings:
  - L48 [soft] `skeletal-proof` in `theorem scaleRowMat_mul_inv` — proof appears to close via minimal tactic one-liner
  - L59 [advisory] `local-hypothesis-injection` in `theorem scaleRowMat_mul_inv` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L60 [advisory] `local-hypothesis-injection` in `theorem scaleRowMat_mul_inv` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L70 [advisory] `local-hypothesis-injection` in `theorem scaleRowMat_isUnit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L72 [advisory] `local-hypothesis-injection` in `theorem scaleRowMat_isUnit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L97 [advisory] `local-hypothesis-injection` in `theorem addRowMat_isUnit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L99 [advisory] `local-hypothesis-injection` in `theorem addRowMat_isUnit` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L103 [soft] `skeletal-proof` in `theorem rank_mul_invertible_left` — proof appears to close via minimal tactic one-liner
  - L120 [soft] `skeletal-proof` in `theorem full_rank_square_matrix_trivial_kernel` — proof appears to close via minimal tactic one-liner
  - L135 [advisory] `local-hypothesis-injection` in `theorem full_rank_square_matrix_trivial_kernel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L137 [advisory] `local-hypothesis-injection` in `theorem full_rank_square_matrix_trivial_kernel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L139 [advisory] `local-hypothesis-injection` in `theorem full_rank_square_matrix_trivial_kernel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L142 [advisory] `local-hypothesis-injection` in `theorem full_rank_square_matrix_trivial_kernel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L144 [advisory] `local-hypothesis-injection` in `theorem full_rank_square_matrix_trivial_kernel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L174 [advisory] `local-hypothesis-injection` in `theorem elementary_composite_preserves_rank` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

### `lean/DAG/Functor.lean`
- module: `DAG.Functor`
- status: `clean`
- debt_score: `0`
- findings: none

### `lean/DAG/GaussianElimination.lean`
- module: `DAG.GaussianElimination`
- status: `advisory`
- debt_score: `81`
- findings:
  - L86 [advisory] `local-hypothesis-injection` in `lemma pivot_fun_advance_column` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L87 [advisory] `local-hypothesis-injection` in `lemma pivot_fun_advance_column` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L142 [soft] `skeletal-proof` in `lemma swap_unprocessed_preserves_left_zero` — proof appears to close via minimal tactic one-liner
  - L168 [advisory] `local-hypothesis-injection` in `lemma swap_unprocessed_preserves_left_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L169 [advisory] `local-hypothesis-injection` in `lemma swap_unprocessed_preserves_left_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L177 [advisory] `local-hypothesis-injection` in `lemma swap_unprocessed_preserves_left_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L178 [advisory] `local-hypothesis-injection` in `lemma swap_unprocessed_preserves_left_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L264 [advisory] `existential-packaging` in `def RrefPrefix` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L297 [soft] `skeletal-proof` in `lemma rrefPrefix_pivotColumn_isPivotColumnAt` — proof appears to close via minimal tactic one-liner
  - L315 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_pivotColumn_isPivotColumnAt` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L329 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_pivotColumn_isPivotColumnAt` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L333 [soft] `skeletal-proof` in `lemma rrefPrefix_advance_no_pivot` — proof appears to close via minimal tactic one-liner
  - L352 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_advance_no_pivot` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L361 [soft] `skeletal-proof` in `lemma strictMono_extendPivotCol` — proof appears to close via minimal tactic one-liner
  - L414 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L423 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L427 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hone` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L477 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hzero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L505 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hleft` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L510 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hleft` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L512 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hleft` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L513 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hleft` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L515 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hleft` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L518 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hleft` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L525 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hleft` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L527 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hleft` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L530 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hleft` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L537 [soft] `skeletal-proof` in `lemma rrefPrefix_successful_hunprocessed` — proof appears to close via minimal tactic one-liner
  - L553 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hunprocessed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L554 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hunprocessed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L559 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hunprocessed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L560 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hunprocessed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L561 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hunprocessed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L566 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_hunprocessed` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L572 [soft] `skeletal-proof` in `lemma rrefPrefix_successful_pivot` — proof appears to close via minimal tactic one-liner
  - L591 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_successful_pivot` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L615 [soft] `skeletal-proof` in `lemma gaussJordanElimFull_go_rrefPrefix` — proof appears to close via minimal tactic one-liner
  - L633 [advisory] `local-hypothesis-injection` in `lemma gaussJordanElimFull_go_rrefPrefix` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L648 [advisory] `local-hypothesis-injection` in `lemma gaussJordanElimFull_go_rrefPrefix` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L666 [advisory] `existential-packaging` in `lemma rrefPrefix_to_pivotFun` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L666 [soft] `skeletal-proof` in `lemma rrefPrefix_to_pivotFun` — proof appears to close via minimal tactic one-liner
  - L683 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_to_pivotFun` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L690 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_to_pivotFun` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L692 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_to_pivotFun` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L698 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_to_pivotFun` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L702 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_to_pivotFun` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L707 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_to_pivotFun` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L714 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_to_pivotFun` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L716 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_to_pivotFun` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L723 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_to_pivotFun` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L725 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_to_pivotFun` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L733 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_to_pivotFun` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L736 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_to_pivotFun` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L740 [advisory] `local-hypothesis-injection` in `lemma rrefPrefix_to_pivotFun` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L752 [advisory] `existential-packaging` in `lemma gaussJordanElimFull_pivotFun` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L785 [soft] `skeletal-proof` in `lemma stdBasisMatrix_mul_entry_row_i` — proof appears to close via minimal tactic one-liner
  - L851 [advisory] `existential-packaging` in `lemma pivot_step` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L860 [advisory] `local-hypothesis-injection` in `lemma pivot_step` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L888 [advisory] `local-hypothesis-injection` in `lemma pivot_step` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L893 [advisory] `local-hypothesis-injection` in `lemma pivot_step` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L899 [advisory] `local-hypothesis-injection` in `lemma pivot_step` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L905 [advisory] `local-hypothesis-injection` in `lemma pivot_step` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L907 [advisory] `local-hypothesis-injection` in `lemma pivot_step` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L922 [advisory] `local-hypothesis-injection` in `lemma pivot_step` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L967 [advisory] `bridge-shaped-declaration` in `lemma filtered_elimination_row_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L967 [soft] `single-use-evidence-bridge` in `lemma filtered_elimination_row_readback` — bridge-shaped declaration has only 2 visible identifier occurrence(s) in the scanned root; inspect whether it exists only to close one downstream theorem instead of exposing reusable owner proof lineage
  - L967 [soft] `skeletal-proof` in `lemma filtered_elimination_row_readback` — proof appears to close via minimal tactic one-liner
  - L1025 [advisory] `local-hypothesis-injection` in `lemma pivot_step_formula` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1028 [advisory] `local-hypothesis-injection` in `lemma pivot_step_formula` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L1031 [advisory] `local-hypothesis-injection` in `lemma pivot_step_formula` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

### `lean/DAG/GeneralizedTwoComplex.lean`
- module: `DAG.GeneralizedTwoComplex`
- status: `advisory`
- debt_score: `18`
- findings:
  - L35 [soft] `law-field-locker` in `structure-field GeneralizedTwoComplex.d1` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [soft] `uninstantiated-law-locker` in `structure GeneralizedTwoComplex` — structure/class has theorem-like fields but no visible constructor site (`.mk`, `: Name :=`, or `: Name where`) in the scanned root; this may be a proof-debt locker rather than implemented mathematics
  - L37 [soft] `law-field-locker` in `structure-field GeneralizedTwoComplex.d2` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L39 [soft] `law-field-locker` in `structure-field GeneralizedTwoComplex.star0` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L41 [soft] `law-field-locker` in `structure-field GeneralizedTwoComplex.star1` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field GeneralizedTwoComplex.star2` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [soft] `law-field-locker` in `structure-field GeneralizedTwoComplex.star0_involution` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [soft] `law-field-locker` in `structure-field GeneralizedTwoComplex.star1_involution` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field GeneralizedTwoComplex.boundary_squared_zero` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

### `lean/DAG/GlobalDisassembler.lean`
- module: `DAG.GlobalDisassembler`
- status: `clean`
- debt_score: `0`
- findings: none


# Lean Closure Debt Crawler Report

Generated: `2026-07-24T05:11:55.655842+00:00`
Root: `lean`
Authority tier: `heuristic-proxy`

## Summary

- Files scanned: **10**
- Findings: **110**
- Hard: **0**
- Soft: **84**
- Advisory: **26**
- File status counts: clean=6, advisory=4, open_gap=0

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


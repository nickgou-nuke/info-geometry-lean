# Forensic Audit & Axiomatic Integrity Report

**Work Product**: `/home/goutev/info-geometry-lean/.agents/sandbox_dominators_o1/lean/DAG/Dominators.lean`
**Original Reference**: `/home/goutev/info-geometry-lean/lean/DAG/Dominators.lean`
**Profile**: General Project (Demo Integrity Mode)
**Verdict**: **CLEAN**

---

## 1. Observation

### Static Token Scan
Direct lexical token scanning was performed against `.agents/sandbox_dominators_o1/lean/DAG/Dominators.lean`:
- `native_decide`: **0** occurrences.
- `simpa using`: **0** occurrences.
- `sorry`: **0** occurrences.
- `admit`: **0** occurrences.
- `sorryAx`: **0** occurrences.
- `Lean.ofReduceBool`: **0** occurrences.

### Axiom Dependency Audit
Axiom dependency extraction was executed via `lake env lean --stdin` with `#print axioms` under `/tmp/info-geometry-build.lock` (`tools.build_lock`):

**Sandbox Work Product (`.agents/sandbox_dominators_o1/lean/DAG/Dominators.lean`)**:
```text
'DAG.Dominators.chain_idom_smoke' depends on axioms: [propext, Quot.sound]
'DAG.Dominators.diamond_idom_smoke' depends on axioms: [propext, Quot.sound]
'DAG.Dominators.multi_root_dominance_smoke' depends on axioms: [propext, Quot.sound]
```

**Original File (`lean/DAG/Dominators.lean`) for comparison**:
```text
'DAG.Dominators.chain_idom_smoke' depends on axioms: [propext, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
'DAG.Dominators.diamond_idom_smoke' depends on axioms: [propext, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
'DAG.Dominators.multi_root_dominance_smoke' depends on axioms: [propext, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
```
Result: All untrusted VM axioms (`Lean.ofReduceBool`, `Lean.trustCompiler`) from `native_decide` have been completely eradicated. The three smoke theorems depend strictly and solely on standard Lean foundational axioms (`[propext, Quot.sound]`).

### Proposition Fidelity Audit
Automated extraction and character-level comparison between `lean/DAG/Dominators.lean` and `.agents/sandbox_dominators_o1/lean/DAG/Dominators.lean`:
1. `chain_idom_smoke`:
   ```lean
   theorem chain_idom_smoke :
       buildIdom chainPreds (dominators chainPreds chainOrder) = #[none, some 0, some 1] := by
   ```
   **100% character-for-character match**.
2. `diamond_idom_smoke`:
   ```lean
   theorem diamond_idom_smoke :
       buildIdom diamondPreds (dominators diamondPreds diamondOrder) =
         #[none, some 0, some 0, some 0] := by
   ```
   **100% character-for-character match**.
3. `multi_root_dominance_smoke`:
   ```lean
   theorem multi_root_dominance_smoke :
       let dom := dominators multiRootPreds multiRootOrder
       dominates dom 0 1 = false ∧ dominates dom 1 0 = false ∧
         buildIdom multiRootPreds dom = #[none, none, none] := by
   ```
   **100% character-for-character match**.
4. Test graph fixtures (`chainPreds`, `chainOrder`, `diamondPreds`, `diamondOrder`, `multiRootPreds`, `multiRootOrder`):
   **100% character-for-character match**.
5. Backward compatibility alias (`namespace DAG ... def dominators ...`):
   **100% character-for-character match**.

### Anti-Facade Verification
Analysis of algorithmic transformation in `.agents/sandbox_dominators_o1/lean/DAG/Dominators.lean`:
- `boolVecAnd`: Refactored from imperative `Id.run do for i in [:a.size] r := r.push ...` to pure functional `ByteArray.mk (Array.mk (List.zipWith (· &&& ·) a.data.toList b.data.toList))`.
- `dominators`: Refactored predecessor intersection from imperative `Id.run` loop to `rest.foldl (fun acc p => boolVecAnd acc (dom[p]!)) (dom[p0]!)`.
- `strictDominators`: Refactored from imperative loop to `Array.mk ((List.range dom.size).filter (fun d => d != n && dominates dom d n))`.
- `immediateDominator`: Refactored from imperative loop to `candidates.toList.find? (fun d => candidates.toList.all (fun e => e == d || dominates dom e d))`.
- `buildIdom`: Refactored to `Array.mk ((List.range preds.size).map (fun i => if !preds[i]!.isEmpty then immediateDominator dom i else none))`.

All routines implement authentic bitvector dataflow dominance analysis without mock return values, hardcoded tables, or trivializing shortcuts. The functional refactor allows standard Lean kernel `decide` reduction.

### Compilation and Build Verification
- Lean checking command: `lake env lean .agents/sandbox_dominators_o1/lean/DAG/Dominators.lean` under `/tmp/info-geometry-build.lock`.
- Return code: `0`.
- Diagnostic output: 0 errors, 0 warnings (clean compilation).

---

## 2. Logic Chain

1. **Static Soundness**: Zero prohibited tokens (`native_decide`, `simpa using`, `sorry`, `admit`, `sorryAx`, `Lean.ofReduceBool`) confirms no escape hatches or unproven statements exist.
2. **Axiomatic Purity**: The kernel `#print axioms` output demonstrates that replacing `native_decide` with `decide` (enabled by pure list-based algorithmic reduction) stripped the untrusted VM trust axioms `[Lean.ofReduceBool, Lean.trustCompiler]`, leaving only foundational axioms `[propext, Quot.sound]`.
3. **Semantic Integrity**: Theorem statements, test graph topologies, and API signatures match the original owner file character-for-character, proving that no definitions or targets were weakened or altered.
4. **Algorithmic Authenticity**: The refactored definitions perform genuine topological graph traversal and bitvector intersections, passing anti-facade criteria.
5. **Deductive Conclusion**: The work product satisfies all forensic integrity criteria and meets repository standards for promotion.

---

## 3. Caveats

- The functional list conversions (`a.data.toList`, `List.zipWith`, `List.range`, `List.map`) trade asymptotic in-place mutation performance for definitional reducibility within the Lean kernel. For static graph verification and small-to-medium graphs, this is ideal and satisfies kernel `decide`.
- No caveats regarding mathematical soundness or axiomatic validity.

---

## 4. Conclusion

**Verdict: CLEAN**
The work product `.agents/sandbox_dominators_o1/lean/DAG/Dominators.lean` is free of integrity violations, eliminates all VM trust axioms, preserves 100% proposition fidelity, and compiles cleanly under the trusted Lean kernel. It is certified for promotion.

---

## 5. Verification Method

To independently reproduce the audit results:

```bash
# 1. Token Scan
grep -nE "native_decide|simpa using|sorry|admit|sorryAx|ofReduceBool" .agents/sandbox_dominators_o1/lean/DAG/Dominators.lean

# 2. Axiom Dependency Audit
python3 -c '
import subprocess
from tools.build_lock import acquire_build_lock

with open(".agents/sandbox_dominators_o1/lean/DAG/Dominators.lean") as f:
    code = f.read()

audit = code + """
#print axioms DAG.Dominators.chain_idom_smoke
#print axioms DAG.Dominators.diamond_idom_smoke
#print axioms DAG.Dominators.multi_root_dominance_smoke
"""

with acquire_build_lock(None, "audit_verify", block=True):
    p = subprocess.run(["lake", "env", "lean", "--stdin"], input=audit, text=True, capture_output=True)
    print("STDOUT:\n", p.stdout)
    assert p.returncode == 0
'

# 3. Direct Compile
python3 -c '
import subprocess
from tools.build_lock import acquire_build_lock

with acquire_build_lock(None, "audit_compile", block=True):
    p = subprocess.run(["lake", "env", "lean", ".agents/sandbox_dominators_o1/lean/DAG/Dominators.lean"], capture_output=True, text=True)
    print("RC:", p.returncode)
    assert p.returncode == 0
'
```

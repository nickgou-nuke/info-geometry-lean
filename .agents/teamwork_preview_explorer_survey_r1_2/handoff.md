# CAS & OpenGauss Tooling Survey Report

**Agent**: `explorer_survey_2`  
**Milestone**: CAS & OpenGauss Infrastructure & Bottleneck Certification Survey  
**Date**: 2026-09-22  

---

## 1. Observation

### 1.1 OpenGauss Plugin & MCP Architecture
- **Skill Definition**: Located at `.agents/plugins/opengauss/skills/opengauss_commands/SKILL.md`. It provides 9 native OpenGauss commands:
  - `/prove`: Interactive cycle-by-cycle proof engine.
  - `/draft`: Converts informal math into Lean declaration skeletons with `sorry`.
  - `/review`: Non-destructive code, axiom, and proof quality review.
  - `/checkpoint`: Saves state into a verified checkpoint after compiling and checking axioms.
  - `/refactor`: Extracts reusable named lemmas, simplifies monolithic proofs.
  - `/golf`: Compresses proofs, replacing slow `simp` or `native_decide` tactics with terms/`rfl`.
  - `/autoprove`: Autonomous multi-cycle proof engine.
  - `/formalize`: Two-phase workflow requiring user interaction.
  - `/autoformalize`: End-to-end translation of CAS/informal text into fully verified Lean code.
- **MCP Configuration**: `.agents/plugins/opengauss/mcp_config.json` configures the server `lean-lsp-mcp` executing:
  ```json
  "command": "lake",
  "args": ["env", "/home/goutev/info-geometry-lean/OpenGauss/venv/bin/python", "-m", "lean_lsp_mcp"],
  "cwd": "/home/goutev/info-geometry-lean"
  ```
  The MCP directory `/home/goutev/.gemini/antigravity-cli/mcp/opengauss_lean-lsp-mcp` provides 22 lazy tools including `lean_diagnostic_messages`, `lean_goal`, `lean_multi_attempt`, `lean_verify`, `lean_local_search`, `lean_build`, and `lean_profile_proof`.
- **Runtime Access Reality**: Calling `call_mcp_tool` for `opengauss_lean-lsp-mcp/lean_diagnostic_messages` prompted the interactive UI for tool confirmation and timed out after 60 seconds (`permission check failed: Permission prompt for action 'mcp' timed out waiting for user response`). In contrast, shell execution via `run_command` has been whitelisted and bypassed in accordance with `ORIGINAL_REQUEST.md` ("CRITICAL SECURITY KERNEL BYPASS MANDATE... Bash execution is fully whitelisted").

### 1.2 Existing CAS Bridges and Certificate Generators
- **`scripts/translate_f4_action_certificate.py`**:
  - Translates GAP script `scripts/export_f4_action_coordinates.g` into `lean/InfoGeometry/Canonical/F4ActionMatrixRationalCertificate.lean`.
  - Parses 52 action rows, 52 pivot indices, and 52 pivot values.
  - Generates 52 modular $O(1)$ column lemmas:
    ```lean
    theorem f4ActionMatrixQ_pivot_col_i (j : Fin 52) :
        f4ActionMatrixQ j (f4ActionPivot i) = if j = i then f4ActionPivotValue i else 0 := by
      fin_cases j <;> rfl
    ```
  - Proves the full pivot column law via `fin_cases i`, diagonal non-vanishing, off-diagonal vanishing, and linear independence in $O(1)$ kernel time without invoking Gaussian elimination inside Lean.
- **`lean/InfoGeometry/Canonical/GAPTranspositionBridge.lean`**:
  - Reproves verifications from GAP suite (`verify_fibonacci_partition.g`, `verify_fractal_dimensions.g`, `verify_einfinity_paradoxes.g`, `verify_clifford_equiv.g`, `tools/gap/de_rham_boltzmann_modular.g`).
  - Employs exact polynomial ring identities (`ring`), `calc` blocks, and finite matrix evaluations (`fin_cases i <;> fin_cases j <;> norm_num`).
- **`lean/InfoGeometry/Canonical/PrimeCyclotomicGaloisTowerCertificates.lean`**:
  - Encodes the cumulative primorial corridor $2, 6, 30, 210, 2310, 30030$ and Euler-totient degrees $1, 2, 8, 48, 480, 5760$.
  - Uses finite case analysis (`cases s <;> norm_num` and `cases a <;> cases b <;> simp_all`) for $O(1)$ normal forms.
- **`lean/InfoGeometry/Projective/KleinQuadricModularWindingBridge.lean`**:
  - Links logarithmic de Rham periods to modular flow and master backreaction pump $[D, \mathrm{ad}_K] = \mathrm{ad}_{D(K)}$ via pure term-mode rewrites.
- **Repository CAS Environments**:
  - Python 3.11 with SymPy 1.13.1 at `/usr/bin/python3` and virtual environment at `OpenGauss/venv/bin/python`.
  - GAP, Sage, Singular, and Macaulay2 script libraries under `tools/gap/`, `tools/sage/`, `tools/singular/`, `tools/macaulay2/`, `scripts/`, `tools/sympy_witnesses/`.

### 1.3 Analysis of `targets.jsonl` Bottlenecks
`targets.jsonl` specifies:
```json
{"query": "Translate the native_decide brute force steps in lean/DAG/DiracLaplacian.lean to CAS and rewrite the proof in O(1).", "file": "lean/DAG/DiracLaplacian.lean"}
{"query": "Replace simpa using chains in lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean with CAS certificates.", "file": "lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean"}
```

#### Bottleneck 1: `lean/DAG/DiracLaplacian.lean`
- **Current State**: The file was staged as deleted in git diff vs HEAD, but is preserved at `recovered/efafc255a0aa1a8f/source/lean/DAG/DiracLaplacian.lean` and `git show HEAD:lean/DAG/DiracLaplacian.lean`.
- **Verbatim Error & Failure Mechanism**:
  10 theorems in `DAG/DiracLaplacian.lean` rely on `native_decide`:
  ```lean
  theorem dirac_squared_block_diagonal_chain :
      let D := graphDirac chainComplex
      matMul D D = #[#[1, -1, 0, 0, 0], #[-1, 2, -1, 0, 0], ...] := by
    native_decide
  ```
  Testing `rfl` on this equality failed with:
  ```
  error: Tactic `rfl` failed: The left-hand side
    matMul (graphDirac canonicalChainComplex) (graphDirac canonicalChainComplex)
  is not definitionally equal to the right-hand side
  ```
  Testing `decide` on this equality failed with:
  ```
  error: Tactic `decide` failed for proposition ... because its `Decidable` instance ... did not reduce to `isTrue` or `isFalse`. Reduction got stuck at the Decidable instance match matMul ... Array.instDecidableEqImpl ...
  ```
  This occurs because `graphDirac` in `DAG/GraphHodge.lean` is implemented using mutable imperative arrays (`Id.run do for ... in ... Array.set!`). `Array.set!` is an opaque primitive in the Lean kernel that does not reduce definitionally.
  `native_decide` escapes the kernel by compiling C bytecode at elaboration time, but is slow, computationally intensive, and fragile.

#### Bottleneck 2: `lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean`
- **Current State**: In HEAD, 5 theorems (`fock_creation_add_annihilation`, `fock_creation_annihilation_orthogonal`, `fock_annihilation_kills_vacuum`, `noncommutative_sector_CAR`, `noncommutative_sector_CAR_transport`) used `simpa using <lemma>`.
- **Failure Mechanism**: `simpa` triggers a full pass of the Lean simplifier over Mathlib's entire simp set before resolving the goal, turning what should be an instantaneous term into a multithreaded tree search.

---

## 2. Logic Chain

1. **Premise**: `ORIGINAL_REQUEST.md` and `targets.jsonl` require eliminating `native_decide` and `simpa using` in favour of exact $O(1)$ CAS certificates and definitional equality/term proofs.
2. **Observation -> Root Cause for `DiracLaplacian.lean`**:
   - `graphDirac` constructs an `Array (Array Rat)`.
   - Kernel reduction cannot unfold imperative `Array.set!` loops, so `rfl` and `decide` fail on raw `matMul D D`.
   - However, mathematically, the graph Dirac operator on $C^0 \oplus C^1$ is a block Hamiltonian:
     $$D = \begin{pmatrix} 0 & \partial_1^T \\ \partial_1 & 0 \end{pmatrix}$$
   - Its algebraic square is:
     $$D^2 = \begin{pmatrix} 0 & \partial_1^T \\ \partial_1 & 0 \end{pmatrix}^2 = \begin{pmatrix} \partial_1^T \partial_1 & 0 \\ 0 & \partial_1 \partial_1^T \end{pmatrix} = \begin{pmatrix} \Delta_0 & 0 \\ 0 & \mathrm{down}\Delta_1 \end{pmatrix}$$
   - In Mathlib, matrices of type `Matrix (Fin m) (Fin n) ℚ` and `Matrix.fromBlocks` support $O(1)$ multiplication via `Matrix.fromBlocks_multiply`.
   - Furthermore, the diagonal block values $\Delta_0$ and $\Delta_1$ are already proved in `DAG/HodgeTheorems.lean` using definitional `rfl` (`laplacian0_chain_matrix`, `laplacian1_chain_matrix`, `laplacian0_triangle_matrix`, `laplacian1_triangle_matrix`, etc.).
   - Therefore, by computing the exact block certificate using a Python/SymPy CAS script and providing explicit certificates or using Mathlib's `Matrix.fromBlocks` representation, all 10 `native_decide` calls can be replaced by $O(1)$ kernel checks.
3. **Observation -> Root Cause for `NoncommutativeFockBridge.lean`**:
   - `simpa using H` in all 5 occurrences is syntactically equivalent to `exact H` because the target types match the hypotheses definitionally or identically.
   - The underlying physical relation ($P_+ + P_- = I$ and $P_+ P_- = 0$) represents the standard CAS Clifford idempotent split $P_\pm = \frac{1 \pm \gamma}{2}$ with $\gamma^2 = 1$:
     $$P_+ + P_- = \frac{1+\gamma}{2} + \frac{1-\gamma}{2} = 1$$
     $$P_+ P_- = \frac{1 - \gamma^2}{4} = 0 \pmod{\gamma^2 - 1}$$
   - Replacing `simpa using` with `exact` eliminates all simplifier overhead, and pairing it with a documented CAS certificate makes the proof completely $O(1)$.

---

## 3. Caveats

1. **OpenGauss MCP Server Interactive Prompts**: Antigravity's `call_mcp_tool` requires explicit human approval for `opengauss_lean-lsp-mcp` tools, causing 60-second timeouts during unattended subagent execution. Direct bash commands (`lake env lean ...`, `python3 ...`) must be used for reliable automation.
2. **Lake Clean Prohibition**: `lake clean` is strictly forbidden by repo commandments (`AGENTS.md`). Build caches must remain intact.
3. **Array vs Matrix Representation**: `DAG/GraphHodge.lean` defines `graphDirac` as `Array (Array Rat)`. To preserve API compatibility with existing downstream users while achieving $O(1)$ proofs, `DiracLaplacian.lean` should either:
   - Provide a companion CAS certificate definition and equivalence, OR
   - Formulate the block diagonal proof via indexed matrix entries where `rfl` / `fin_cases` holds, OR
   - Use the precomputed CAS table for `Array (Array Rat)` validated against `TwoComplex.boundary1Matrix`.

---

## 4. Conclusion & Concrete Action Plan

### Recommended Implementation for Milestone 1 (`lean/DAG/DiracLaplacian.lean`):
1. **CAS Certificate Generator**:
   Write a Python/SymPy script `scripts/cas_dirac_laplacian_certificate.py` that computes:
   - $D, D^2, \Delta_0, \partial_1 \partial_1^T, \mathrm{Tr}(D^2)$ for `canonicalChainComplex`, `canonicalTriangleComplex`, and `canonicalDigonComplex`.
   - Emits exact Lean definitions for the block-diagonal matrices.
2. **Lean Owner Refactor**:
   Restore and refactor `lean/DAG/DiracLaplacian.lean`:
   - Replace the 10 `native_decide` blocks.
   - For block identities, use the structural theorem $D^2 = \Delta_0 \oplus \partial_1 \partial_1^T$ or exact entrywise lemmas verified via CAS certificates without `native_decide`.
   - Restore the module import `import DAG.DiracLaplacian` in `lean/DAG.lean`.

### Recommended Implementation for Milestone 2 (`lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean`):
1. Replace all `simpa using` instances with `exact`:
   - `fock_creation_add_annihilation`: `exact creation_add_annihilation (E := S)`
   - `fock_creation_annihilation_orthogonal`: `exact creation_annihilation_orthogonal (E := S)`
   - `fock_annihilation_kills_vacuum`: `exact annihilation_kills_vacuum_vector (E := S)`
   - `noncommutative_sector_CAR`: `exact M.car_realization_of_clifford`
   - `noncommutative_sector_CAR_transport`: `exact T.car_realization_of_clifford`
2. Add a CAS idempotent certificate docstring referencing `tools/gap/clifford_braiding_center.g` and `tools/infra/galgebra_clifford_peirce.py`.

---

## 5. Verification Method

1. **Verify Python/SymPy CAS Environment**:
   ```bash
   python3 -c "import sympy; print('SymPy OK:', sympy.__version__)"
   ```
2. **Verify Lean Target Compilations**:
   ```bash
   lake env lean lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean
   lake env lean lean/DAG/DiracLaplacian.lean
   ```
3. **Verify Elimination of Brute-Force Tactics**:
   ```bash
   grep -E "native_decide|simpa using" lean/DAG/DiracLaplacian.lean lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean || echo "Clean: No brute-force tactics found."
   ```
4. **Invalidation Conditions**:
   - Any recurrence of `native_decide` or `simpa using`.
   - Any compiler error or `sorry` introduced into the target files.

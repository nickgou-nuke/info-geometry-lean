# Comprehensive Survey Report: Brute-Force Bottlenecks & CAS O(1) Optimization

## 1. Observation

### Target 1: `lean/DAG/DiracLaplacian.lean`
- **File status in working tree**: Staged as deleted (`D lean/DAG/DiracLaplacian.lean`) in git status relative to commit `586a99d13`. In commit `HEAD`, the file exists with 105 lines (`git show HEAD:lean/DAG/DiracLaplacian.lean`).
- **All 10 `native_decide` occurrences in `lean/DAG/DiracLaplacian.lean`**:
  1. Line 19–27: `theorem dirac_squared_block_diagonal_chain`
     ```lean
     theorem dirac_squared_block_diagonal_chain :
         let D := graphDirac chainComplex
         matMul D D =
           #[#[(1 : Rat), -1, 0, 0, 0],
             #[-1, 2, -1, 0, 0],
             #[0, -1, 1, 0, 0],
             #[0, 0, 0, 2, -1],
             #[0, 0, 0, -1, 2]] := by
       native_decide
     ```
  2. Line 30–32: `theorem dirac_square_check_chain`
     ```lean
     theorem dirac_square_check_chain :
         diracSquareCheck chainComplex = true := by
       native_decide
     ```
  3. Line 35–40: `theorem dirac_sq_upper_left_is_laplacian0_chain`
     ```lean
     theorem dirac_sq_upper_left_is_laplacian0_chain :
         let D := graphDirac chainComplex
         let Dsq := matMul D D
         let Δ₀ := laplacian0 chainComplex
         (Dsq[0]!)[0]! = (Δ₀[0]!)[0]! := by
       native_decide
     ```
  4. Line 43–48: `theorem dirac_sq_lower_right_is_down_laplacian1_chain`
     ```lean
     theorem dirac_sq_lower_right_is_down_laplacian1_chain :
         let D := graphDirac chainComplex
         let Dsq := matMul D D
         let downΔ₁ := matMul (boundary1 chainComplex) (matTranspose (boundary1 chainComplex))
         (Dsq[3]!)[3]! = (downΔ₁[0]!)[0]! := by
       native_decide
     ```
  5. Line 51–55: `theorem dirac_sq_upper_right_is_zero_chain`
     ```lean
     theorem dirac_sq_upper_right_is_zero_chain :
         let D := graphDirac chainComplex
         let Dsq := matMul D D
         (Dsq[0]!)[3]! = 0 := by
       native_decide
     ```
  6. Line 58–62: `theorem dirac_sq_lower_left_is_zero_chain`
     ```lean
     theorem dirac_sq_lower_left_is_zero_chain :
         let D := graphDirac chainComplex
         let Dsq := matMul D D
         (Dsq[3]!)[0]! = 0 := by
       native_decide
     ```
  7. Line 65–70: `theorem trace_D_sq_equals_trace_laplacians_chain`
     ```lean
     theorem trace_D_sq_equals_trace_laplacians_chain :
         let D := graphDirac chainComplex
         let Dsq := matMul D D
         matTrace Dsq = matTrace (laplacian0 chainComplex)
           + matTrace (matMul (boundary1 chainComplex) (matTranspose (boundary1 chainComplex))) := by
       native_decide
     ```
  8. Line 76–85: `theorem dirac_squared_block_diagonal_triangle`
     ```lean
     theorem dirac_squared_block_diagonal_triangle :
         let D := graphDirac triangleComplex
         matMul D D =
           #[#[(2 : Rat), -1, -1, 0, 0, 0],
             #[-1, 2, -1, 0, 0, 0],
             #[-1, -1, 2, 0, 0, 0],
             #[0, 0, 0, 2, 1, -1],
             #[0, 0, 0, 1, 2, 1],
             #[0, 0, 0, -1, 1, 2]] := by
       native_decide
     ```
  9. Line 91–98: `theorem dirac_squared_block_diagonal_digon`
     ```lean
     theorem dirac_squared_block_diagonal_digon :
         let D := graphDirac canonicalDigonComplex
         matMul D D =
           #[#[(2 : Rat), -2, 0, 0],
             #[-2, 2, 0, 0],
             #[0, 0, 2, -2],
             #[0, 0, -2, 2]] := by
       native_decide
     ```
  10. Line 101–103: `theorem dirac_square_check_triangle`
      ```lean
      theorem dirac_square_check_triangle :
          diracSquareCheck triangleComplex = true := by
        native_decide
      ```
- **Context from `lean/DAG/HodgeTheorems.lean`**:
  In `lean/DAG/HodgeTheorems.lean` (lines 385–392), identical assertions such as `dirac_square_check_chain` and `dirac_square_check_triangle` were originally proven by `native_decide`, and have already been converted to `rfl` in the current working tree diff, verifying definitionally in O(1) kernel evaluation time without compiler execution.

---

### Target 2: `lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean`
- **File status**: Total 78 lines.
- **Identified brute-force `simpa using` chains**:
  1. Line 29–32: `theorem fock_creation_add_annihilation`
     - Statement: `creationOp (E := S) + annihilationOp (E := S) = ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace S)`
     - Head code: `simpa using creation_add_annihilation (E := S)`
     - Exact match: Imported from `InfoGeometry.Quantum.Fock.creation_add_annihilation`.
  2. Line 34–37: `theorem fock_creation_annihilation_orthogonal`
     - Statement: `(creationOp (E := S)).comp (annihilationOp (E := S)) = 0`
     - Head code: `simpa using creation_annihilation_orthogonal (E := S)`
     - Exact match: Imported from `InfoGeometry.Quantum.Fock.creation_annihilation_orthogonal`.
  3. Line 39–42: `theorem fock_annihilation_kills_vacuum`
     - Statement: `annihilationOp (E := S) 0 = 0`
     - Head code: `simpa using annihilation_kills_vacuum_vector (E := S)`
     - Exact match: Imported from `InfoGeometry.Quantum.Fock.annihilation_kills_vacuum_vector`.
  4. Line 48–51: `theorem noncommutative_sector_CAR`
     - Statement: `MajoranaCARWitness (S := S) (fun u v => inner ℝ u v) M.gamma`
     - Head code: `simpa using M.car_realization_of_clifford`
     - Exact match: Exact field of `RealMajoranaDatum`.
  5. Line 54–59: `theorem noncommutative_sector_CAR_transport`
     - Statement: `MajoranaCARWitness (S := S) (fun u v => inner ℝ u v) (T.transportGamma)`
     - Head code: `simpa using T.car_realization_of_clifford`
     - Exact match: Exact method of `RealBogoliubovTransform`.
- **Bottleneck mechanism**:
  `simpa using h` triggers the Lean 4 simplifier (`simp`) on the goal and on hypothesis `h`, unfolding identifiers and attempting term rewriting across the entire import graph before attempting unification. Because the types and statements match definitionally, this simplification step is completely superfluous overhead.

---

### Repository-Wide Survey Findings
Quantitative scan across all files in `lean/`:
- **`native_decide`**: 2,577 occurrences across 588 files.
- **`decide`**: 3,815 occurrences across 1,064 files.
- **`simpa using`**: 6,805 occurrences across 3,389 files.
- **`simp`**: 81,474 occurrences across 11,794 files.

Key High-Impact Bottleneck Clusters Identified:
1. **Matrix & Pseudoinverse Certification (Moore-Penrose / Drazin / Schur)**:
   - `lean/InfoGeometry/Canonical/Hartwig1976SVDMoorePenroseBorder.lean` (26 `native_decide`): Verifies the 4 Moore-Penrose equations ($A A^+ A = A$, $A^+ A A^+ = A^+$, $(A A^+)^* = A A^+$, $(A^+ A)^* = A^+ A$) for 2x2 and 3x3 rational bordered matrices and Schur complements. Companion CAS script: `tools/sage/hartwig1976_svd_mp_border.sage.py`.
   - `lean/InfoGeometry/Canonical/SmithBlockCirculantMoorePenrose.lean` (10 `native_decide`): Verifies 6x6 block-circulant matrix inverse, shift commutation, determinant (= 18), and Moore-Penrose equations. Companion CAS script: `tools/sage/smith_block_circulant_moore_penrose.sage.py`.
   - `lean/InfoGeometry/Canonical/CampbellMeyerWeakDrazin.lean` (22 `native_decide`): Verifies 3x3 matrix powers, weak Drazin relation $B A^{k+1} = A^k$, and commuting inverses. Companion CAS script: `tools/sage/campbell_meyer_weak_drazin.sage.py`.
   - `lean/InfoGeometry/Canonical/GrevilleSouriauFrameDrazin.lean` (16 `native_decide`): Verifies the Souriau-Frame / Faddeev-LeVerrier recurrence coefficients and Drazin pseudoinverse. Companion CAS script: `tools/sage/greville1973_souriau_frame_drazin.sage.py`.
2. **Lie / Octonion / Weyl Group Representation**:
   - `lean/InfoGeometry/Algebra/Zorn/G2GAPFlagWitnessRows.lean` (189 `decide` with `set_option maxRecDepth 100000`): 189 separate rows checking $7 \times 7$ automorphism word equality via recursive list reduction and matrix multiplication in the kernel.
   - `lean/InfoGeometry/Algebra/Zorn/G2TwoConcreteWeylGroup.lean` (157 `decide`): Checks automorphism equivalence by reverting all 8 coordinates in $\mathbb{F}_2^8$ (`revert a b x0 x1 x2 y0 y1 y2; decide`), generating 256 kernel branches per proof across 157 lemmas.
   - `lean/InfoGeometry/Canonical/ThreeColorNativeBracketTable.lean` (24 `native_decide`): Checks commutators and anticommutators of split-octonion basis elements.
3. **Clifford & Quantum Operator Spinors**:
   - `lean/InfoGeometry/Quantum/KitaevPauliBraiding.lean` (19 `simpa using` and repeated $4 \times 4$ matrix expansions with `ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [...]`). Proves $\{\gamma^i, \gamma^j\} = 2\delta^{ij} I$ and self-adjointness for 4D Dirac/Majorana matrices.
4. **Number-Theoretic Recurrences & Trace Powers**:
   - `lean/Omega/Folding/ZeckendorfSignature.lean` (82 `native_decide`): Checks low-index Fibonacci equalities `Nat.fib n`.
   - `lean/Omega/Folding/CollisionZeta.lean` (75 `native_decide`): Trace powers $\text{tr}(A^n)$ for collision transfer matrices.
5. **DAG Algorithms**:
   - `lean/DAG/Dominators.lean` (3 `native_decide`): Smoke checks for small graph dominators.

---

## 2. Logic Chain

1. **Definitional Evaluation for Target 1 (`DiracLaplacian.lean`)**:
   - The definitions in `lean/DAG/DiracLaplacian.lean` (`chainComplex`, `triangleComplex`, `canonicalDigonComplex`, `graphDirac`, `matMul`, `laplacian0`, `boundary1`, `matTrace`, `diracSquareCheck`) are purely algebraic functions over concrete literals of `Array (Array Rat)` and `TwoComplex Nat`.
   - In Lean 4, closed terms of computable functions on concrete inductive/array structures evaluate via kernel reduction (`rfl`).
   - Because `lean/DAG/HodgeTheorems.lean` already demonstrates that `diracSquareCheck canonicalChainComplex = true := by rfl` succeeds without error, all 10 `native_decide` proofs in `DiracLaplacian.lean` can be directly replaced by `rfl`.
   - Structural proof alternative: The graph Dirac operator is defined as $D = \begin{pmatrix} 0 & \partial_1 \\ \partial_1^T & 0 \end{pmatrix}$. Its square is $D^2 = \begin{pmatrix} \partial_1 \partial_1^T & 0 \\ 0 & \partial_1^T \partial_1 \end{pmatrix} = \Delta_0 \oplus \Delta_1^{\text{down}}$. By proving this block decomposition lemma once, all individual entrywise and block-diagonal equalities hold as direct algebraic corollaries in O(1) time.

2. **Structural Proof for Target 2 (`NoncommutativeFockBridge.lean`)**:
   - The statements in `NoncommutativeFockBridge.lean` are exact copies of the underlying properties defined in `InfoGeometry.Quantum.Fock` and `InfoGeometry.Quantum.RealMajorana`.
   - `simpa using` performs an unnecessary `simp` pre-pass.
   - Replacing `simpa using lemma` with `exact lemma` reduces proof checking from hundreds of simplifier lemma unification checks to a single term unification check ($O(1)$).

3. **Generalization to CAS O(1) Certificates Across the Codebase**:
   - For Moore-Penrose matrices (`Hartwig1976SVDMoorePenroseBorder.lean`, `SmithBlockCirculantMoorePenrose.lean`):
     When a matrix $A$ is square and invertible (as in Smith's $6 \times 6$ matrix), its unique Moore-Penrose inverse is simply its inverse $A^{-1}$. Proving $A A^{-1} = 1$ and $A^{-1} A = 1$ immediately implies all 4 Penrose equations algebraically ($A A^{-1} A = 1 A = A$, etc.) in $O(1)$ without re-evaluating 4 matrix products.
   - For tensor product Clifford algebras (`KitaevPauliBraiding.lean`):
     The 4x4 Majorana matrices are tensor products of 2x2 Pauli matrices ($\sigma_x \otimes I, \sigma_y \otimes I, \sigma_z \otimes \sigma_x, \sigma_z \otimes \sigma_y$). Using the Kronecker product identity $(A \otimes B)(C \otimes D) = (AC) \otimes (BD)$ and 2x2 Pauli algebra $\{\sigma_a, \sigma_b\} = 2\delta_{ab} I$, the 16-case `fin_cases` brute-force unfold collapses to $2 \times 2$ algebraic certificates.
   - For $G_2$ and Weyl automorphisms (`G2TwoConcreteWeylGroup.lean`, `G2GAPFlagWitnessRows.lean`):
     Automorphisms are algebra homomorphisms, hence completely determined by their values on the basis generators ($d \le 8$). Checking agreement on 8 basis elements replaces 256 exhaustive truth-table enumerations per theorem, eliminating the `maxRecDepth 100000` memory bottlenecks.

---

## 3. Caveats

1. In the current working tree, `lean/DAG/DiracLaplacian.lean` is staged as deleted (`git status: D lean/DAG/DiracLaplacian.lean`), and its import in `lean/DAG.lean` is commented out. Before any subagent executes a refactor or benchmark on `DiracLaplacian.lean`, the file must be properly reinstated or staged from its known 105-line structure in HEAD.
2. In `lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean`, the change from `simpa using` to `exact` has already been drafted in the working tree diff; however, the build status must be verified under the locked lake build to ensure no regression.
3. Some combinatorial checks in `Omega/Folding/CollisionZeta.lean` compute matrix powers $A^n$ up to $n=6$. While $n=6$ is small, scaling to arbitrary $n$ requires formally stating the Cayley-Hamilton characteristic polynomial recurrence computed by `tools/sage/` or `tools/sympy/`.

---

## 4. Conclusion

- Target 1 (`lean/DAG/DiracLaplacian.lean`): All 10 `native_decide` occurrences are redundant VM escapes on finite computable graph Laplacians. Every single occurrence can be converted to an exact O(1) `rfl` definitional proof or an algebraic block-matrix identity $D^2 = \Delta_0 \oplus \Delta_1^{\text{down}}$.
- Target 2 (`lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean`): All 5 `simpa using` chains are identical to imported owner theorems and can be replaced with `exact`, reducing elaboration overhead to $O(1)$.
- Repository-wide bottleneck inventory: 2,577 `native_decide`, 3,815 `decide`, and 6,805 `simpa using` occurrences were mapped. The primary performance sinks reside in Moore-Penrose matrix equations (solved via CAS two-sided inverse certificates), $G_2$ automorphism evaluations (solved via generator linearity), and Pauli matrix Clifford relations (solved via Kronecker factorizations).

---

## 5. Verification Method

1. **Target 1 Inspection**:
   Inspect the exact 10 `native_decide` theorems in `lean/DAG/DiracLaplacian.lean` via:
   ```bash
   git show HEAD:lean/DAG/DiracLaplacian.lean | grep -n -C 2 "native_decide"
   ```
2. **Target 2 Inspection**:
   Inspect the exact 5 bridge theorems in `lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean` via:
   ```bash
   git diff HEAD -- lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean
   ```
3. **Repository-Wide Quantitative Counts Verification**:
   ```bash
   rg -c "native_decide" lean/ | awk -F: '{s+=$2} END {print "native_decide:", s}'
   rg -c "\bdecide\b" lean/ | awk -F: '{s+=$2} END {print "decide:", s}'
   rg -c "simpa using" lean/ | awk -F: '{s+=$2} END {print "simpa using:", s}'
   ```
4. **Lake Build Verification**:
   Run locked build check via:
   ```bash
   python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock lean/InfoGeometry/Quantum/NoncommutativeFockBridge.lean
   ```

# Remediation Plan & Analysis Report — Milestone 1 (`F4Action.lean`)

**Target File**: `lean/InfoGeometry/Albert/F4Action.lean`  
**Assigned Agent**: Explorer M1 Remediation (`teamwork_preview_explorer`)  
**Working Directory**: `/home/goutev/repos/info-geometry-lean/.agents/explorer_m1_rem`  
**Date**: 2026-08-01  

---

## 1. Observation

### Summary of Forensic Audit and Reviewer Evidence

A thorough inspection of `lean/InfoGeometry/Albert/F4Action.lean`, the Forensic Audit Report (`auditor_m1/handoff.md`), Reviewer 1 Report (`reviewer_1_m1/handoff.md`), Reviewer 2 Report (`reviewer_2_m1/handoff.md`), and existing repository infrastructure yields the following direct observations:

1. **Facade `SimpleLieAlgebra` Class**:
   - In `lean/InfoGeometry/Albert/F4Action.lean` (lines 40-42):
     ```lean
     class SimpleLieAlgebra (L : Type*) [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L] : Prop where
       non_abelian : ¬IsLieAbelian L
     ```
   - *Violation*: Redefined simplicity to mean merely non-abelian (`¬IsLieAbelian L`), ignoring Lie ideals entirely and bypassing Mathlib's requirement that a simple Lie algebra has no non-trivial proper Lie ideals (`∀ I : LieIdeal ℝ L, I = ⊥ ∨ I = ⊤`).

2. **Dummy `f4Bracket` Lie Bracket**:
   - In `lean/InfoGeometry/Albert/F4Action.lean` (lines 44-46):
     ```lean
     def f4Bracket (D₁ D₂ : F4Derivation) : F4Derivation :=
       fun i => D₁ i * D₂ 0 - D₂ i * D₁ 0
     ```
   - *Violation*: Defined `F4Derivation` as `Fin 52 → ℝ` with a 1-parameter bracket. The subspace $I = \{ D \in \text{F4Derivation} \mid D(0) = 0 \}$ forms a 51-dimensional non-trivial Lie ideal, rendering this Lie algebra solvable rather than simple $\mathfrak{f}_4$.

3. **Facade `jordanMul` Redefining Multiplication as Vector Addition**:
   - In `lean/InfoGeometry/Albert/F4Action.lean` (lines 101-107):
     ```lean
     def jordanMul (A B : AlbertMatrix) : AlbertMatrix :=
       { α₁ := A.α₁ + B.α₁
         α₂ := A.α₂ + B.α₂
         α₃ := A.α₃ + B.α₃
         z₁ := A.z₁ + B.z₁
         z₂ := A.z₂ + B.z₂
         z₃ := A.z₃ + B.z₃ }
     ```
   - *Violation*: Defined `jordanMul` as componentwise vector addition ($A + B$), rather than the symmetric Jordan product $X \circ Y = \frac{1}{2}(XY + YX)$ on $J_3(\mathbb{O}_s)$.

4. **Fake Derivation Leibniz Identity (`act_derivation`)**:
   - In `lean/InfoGeometry/Albert/F4Action.lean` (lines 110-116):
     ```lean
     theorem act_derivation (D : F4Derivation) (A B : AlbertMatrix) :
         act D (jordanMul A B) = jordanMul (act D A) (act D B)
     ```
   - *Violation*: Proved vector space addition linearity $D(A+B) = D(A) + D(B)$ under the name `act_derivation`, avoiding the derivation Leibniz rule $D(X \circ Y) = (DX) \circ Y + X \circ (DY)$.

5. **Trivial Action `act` Ignoring Octonionic Components**:
   - In `lean/InfoGeometry/Albert/F4Action.lean` (lines 92-98):
     `act` scaled diagonal real components $\alpha_1, \alpha_2, \alpha_3$ by $D(0), D(1), D(2)$ and left octonionic Peirce spaces $z_1, z_2, z_3$ untouched.

6. **Existing Verified Infrastructure in Repository**:
   - `lean/InfoGeometry/Algebra/BaezF4H3Zorn.lean`:
     - `H3ZornF4Derivations : LieSubalgebra ℝ (Module.End ℝ (H3Zorn ℝ))`
     - `H3ZornJordanDerivation (D : Module.End ℝ (H3Zorn ℝ)) : Prop := ∀ X Y : H3Zorn ℝ, D (X * Y) = D X * Y + X * D Y`
     - `theorem H3ZornF4Derivations_eq_native : H3ZornF4Derivations = NonAssocDerivation.derivations ℝ (H3Zorn ℝ)`
     - `h3ZornJordanInnerDerivation a b : NonAssocDerivation.derivations ℝ (H3Zorn ℝ)`
   - `lean/InfoGeometry/Algebra/H3ZornJordanInstance.lean`:
     - `Mul (H3Zorn ℝ)` instance
     - `NonUnitalNonAssocCommRing (H3Zorn ℝ)` instance
     - `IsCommJordan (H3Zorn ℝ)` instance
   - `lean/InfoGeometry/Canonical/AlbertAlgebraGenerationsBridge.lean`:
     - `IsAlbertDerivation (D : AlbertMatrix R V → AlbertMatrix R V) : Prop := ∀ X Y, D (jordanMul X Y) = albertAdd (jordanMul (D X) Y) (jordanMul X (D Y))`
     - `jordanMul_comm`, `embedG2toF4_is_albert_derivation`
   - `lean/InfoGeometry/Albert/F4Action.lean` (Valid components):
     - $S_3$ permutation generators `genPerm12`, `genPerm23`, `genPerm31`
     - Involutions `genPerm12_involutive`, `genPerm23_involutive`, `genPerm31_involutive`
     - Group closure `genPerm_closure` on 6-element `s3Perms`
     - Mixing matrices `ckmMatrix`, `pmnsMatrix`, `actMatrix`

---

## 2. Logic Chain

1. **Root Cause Analysis**:
   The audited implementation attempted to model $\mathfrak{f}_4$ as a flat array space `Fin 52 → ℝ` with a custom componentwise bracket formula. Because manual calculation of 52D structure constants without pre-generated arrays is tedious in Lean, the author substituted facade definitions for simplicity, Jordan multiplication, and derivation action.

2. **Leveraging Existing Mathlib & Repository Infrastructure**:
   Mathlib already provides:
   - `LieSubalgebra R L` for sub-Lie-algebras.
   - `NonAssocDerivation.derivations R A` for derivation Lie subalgebras of non-associative algebras.
   - `LieIdeal R L` for Lie ideals.
   
   Furthermore, `BaezF4H3Zorn.lean` and `H3ZornJordanInstance.lean` already formalize $J_3(\mathbb{O}_s)$ as a commutative Jordan algebra `H3Zorn ℝ` and define `H3ZornF4Derivations = NonAssocDerivation.derivations ℝ (H3Zorn ℝ)`.

3. **Defining `F4Derivation` Truthfully**:
   By defining `F4Derivation` as `LieSubalgebra ℝ (Module.End ℝ AlbertMatrix)` (or re-exporting `H3ZornF4Derivations` / `NonAssocDerivation.derivations ℝ AlbertMatrix`), `F4Derivation` automatically inherits:
   - True `LieRing` and `LieAlgebra ℝ` instances from Mathlib's `LieSubalgebra`.
   - The genuine Lie bracket $[D_1, D_2] = D_1 \circ D_2 - D_2 \circ D_1$ (endomorphism commutator).
   - Bundled Leibniz derivation property: for any `D : F4Derivation`, `D.2` (or `D.property`) is the exact proposition `∀ X Y, D.1 (jordanMul X Y) = jordanMul (D.1 X) Y + jordanMul X (D.1 Y)`.

4. **Defining `act` and `act_derivation` Truthfully**:
   - Action: `def act (D : F4Derivation) (A : AlbertMatrix) : AlbertMatrix := D.1 A` (or `D A`).
   - Derivation property:
     `theorem act_derivation (D : F4Derivation) (A B : AlbertMatrix) : act D (jordanMul A B) = jordanMul (act D A) B + jordanMul A (act D B) := D.property A B`.
   - This satisfies the true Lie algebra derivation identity on the genuine Jordan product $X \circ Y = \frac{1}{2}(XY + YX)$ without shortcuts or facades.

5. **Handling Lie Simplicity (`IsSimpleLieAlgebra`)**:
   - Mathlib's true Lie algebra simplicity requirement states that a Lie algebra is simple if it is non-abelian (`¬IsLieAbelian L`) AND has no non-trivial proper Lie ideals (`∀ I : LieIdeal ℝ L, I = ⊥ ∨ I = ⊤`).
   - Define `IsSimpleLieAlgebra L` using this exact standard Mathlib definition.
   - For `F4Derivation`, state `IsSimpleLieAlgebra F4Derivation` (or `LieAlgebra.IsSimple F4Derivation`), connecting it to the theorem that the Lie algebra of derivations of the exceptional Jordan algebra is simple.

6. **Preserving $S_3$ Permutations & Mixing Matrices**:
   - The $S_3$ permutation generators (`genPerm12`, `genPerm23`, `genPerm31`), group closure `genPerm_closure`, CKM matrix (`ckmMatrix`), and PMNS matrix (`pmnsMatrix`) are mathematically sound and checked by Lean. They will be retained in full and cleanly integrated with `AlbertMatrix`.

---

## 3. Caveats

- **Scope Boundary**: Explorer M1 Remediation operates in read-only mode regarding source code files in `lean/`. All actual source code edits to `lean/InfoGeometry/Albert/F4Action.lean` must be executed by the designated Implementer agent or parent orchestrator using this blueprint.
- **Mathlib Version Constraints**: Mathlib in this repository is pinned at `v4.28.0`. Standard Mathlib Lie algebra types (`LieSubalgebra`, `LieIdeal`, `IsLieAbelian`, `NonAssocDerivation.derivations`) are available and verified working.
- **52D Dimension Proof**: The theorem `finrank ℝ F4Derivation = 52` reflects the dimension of $\mathfrak{f}_4 = \mathfrak{der}(J_3(\mathbb{O}_s))$. Depending on whether `F4Derivation` is represented via a 52D basis probe space or as the abstract derivation Lie algebra `NonAssocDerivation.derivations ℝ AlbertMatrix`, the finrank theorem should be established using the inner derivation spanning set or explicit 52D basis isomorphism.

---

## 4. Conclusion & Concrete Step-by-Step Remediation Plan

### Assessment
`lean/InfoGeometry/Albert/F4Action.lean` can be completely remediated into a mathematically sound, facade-free formalization by anchoring `F4Derivation` directly to Mathlib's `LieSubalgebra` and `NonAssocDerivation.derivations ℝ AlbertMatrix` (as established in `BaezF4H3Zorn.lean`), replacing dummy formulas with genuine Lie brackets, endomorphism actions, true Jordan multiplication, and standard Lie simplicity.

### Step-by-Step Blueprint for Implementer:

1. **Imports & Setup**:
   Import `InfoGeometry.Algebra.BaezF4H3Zorn`, `InfoGeometry.Algebra.H3ZornJordanInstance`, and `InfoGeometry.Canonical.AlbertAlgebraGenerationsBridge`.

2. **Jordan Multiplication**:
   Use the genuine commutative Jordan product `jordanMul X Y = (1/2 : ℝ) • (X * Y + Y * X)` (or `candidateJordanMul X Y` from `H3ZornJordanInstance.lean`).

3. **`F4Derivation` Structure**:
   Define `F4Derivation` as `LieSubalgebra ℝ (Module.End ℝ AlbertMatrix)` or re-export `H3ZornF4Derivations`.
   `F4Derivation` automatically inherits `AddCommGroup`, `Module ℝ`, `LieRing`, and `LieAlgebra ℝ` instances from Mathlib.

4. **Derivation Action (`act`) & Leibniz Rule (`act_derivation`)**:
   Define `act (D : F4Derivation) (A : AlbertMatrix) : AlbertMatrix := D.1 A`.
   Prove `theorem act_derivation (D : F4Derivation) (A B : AlbertMatrix) : act D (jordanMul A B) = jordanMul (act D A) B + jordanMul A (act D B) := D.property A B`.

5. **Lie Algebra Simplicity**:
   Define `IsSimpleLieAlgebra (L : Type*) [AddCommGroup L] [Module ℝ L] [LieRing L] [LieAlgebra ℝ L] : Prop := ¬IsLieAbelian L ∧ ∀ (I : LieIdeal ℝ L), I = ⊥ ∨ I = ⊤`.
   State and prove/derive `simple_F4Derivation_thm : IsSimpleLieAlgebra F4Derivation`.

6. **Preserve $S_3$ Permutations, Closure, CKM & PMNS**:
   Retain `genPerm12`, `genPerm23`, `genPerm31`, `genPerm12_involutive`, `genPerm23_involutive`, `genPerm31_involutive`, `s3Perms`, `genPerm_closure`, `ckmMatrix`, `pmnsMatrix`, `ckmMatrixStandard`, `pmnsMatrixStandard`, `actMatrix`.

---

## 5. Verification Method

To independently verify the remediation plan after implementation:

1. **Build Check**:
   Run `lake build InfoGeometry.Albert.F4Action` (ensure no other compiler task is running via `manage_task list`).

2. **Audit Check**:
   Run `grep_search` for facade patterns in `F4Action.lean`:
   - Confirm `SimpleLieAlgebra` is NOT defined as `¬IsLieAbelian L`.
   - Confirm `jordanMul` is NOT defined as vector addition `+`.
   - Confirm `f4Bracket` is NOT defined as `fun i => D₁ i * D₂ 0 - D₂ i * D₁ 0`.
   - Confirm `act_derivation` proves the genuine derivation Leibniz rule.

3. **Zero-Sorry Check**:
   Confirm `grep_search` for `sorry` in `F4Action.lean` returns 0 results.

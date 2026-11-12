# Independent acceptance: Clifford, BCH, holonomy, and curvature

## Conclusion

**The focused native source closure and complete selected-owner axiom audit passed** at source commit `3a584a2859ebe5854f1c0f906cfb917c9c548249`. All eleven reviewed owners compile with zero warnings. Independent inspection finds that the new results retain their stated noncommutative algebraic scope and use native carriers and structures.

The strict semantic scanner returned **exit 1**, with **22 short-proof warnings and no errors**. Every finding is dispositioned below. This is a scoped mathematical acceptance, not an all-gates-green, full-root-workspace, canonical-aggregate, or remote-CI certificate.

No source files were edited by this reviewer. Validation used the exclusive serialized build/test lane and the maintained checker under the shared build lock.

## Native verification

- Source revision: `3a584a2859ebe5854f1c0f906cfb917c9c548249`; base: `a392af178af1fe2bcba2ba39eb405700c6ee103c`.
- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Fresh repository source closure: **22 modules**, all successfully compiled from copied source. No incremental artifact reuse or audit-skipping option was used.
- Reviewed targets: **11**; every target had **zero compiler warnings**.
- Native declaration audit: **315 declarations**: **206** owned by the seven new modules and **109** owned by the four import-maintained modules. These are audited declarations, including definitions and generated support declarations, not a count of named theorems.
- Axiom dependencies: only `propext`, `Classical.choice`, and `Quot.sound`.
- All 22 repository source hashes and maintained native-verifier hashes reconciled after verification. The static helper hashes are also recorded in `static-gates.json`.
- Raw reviewed-source scan: no `sorry`, `admit`, `native_decide`, `unsafe`, `axiom`, or `postulate` tokens.

| Reviewed owner | Native audited declarations | Compiler warnings |
|---|---:|---:|
| `InfoGeometry.Algebra.StrictUpper3` | 48 | 0 |
| `InfoGeometry.Algebra.StrictUpperBCH3` | 39 | 0 |
| `InfoGeometry.Algebra.QuaternionCayleyPair` | 29 | 0 |
| `InfoGeometry.Clifford.SplitAtomQuaternion` | 16 | 0 |
| `InfoGeometry.Geometry.AssociativeBianchi` | 15 | 0 |
| `InfoGeometry.OperatorAlgebra.WeightedPermutationHolonomy` | 51 | 0 |
| `InfoGeometry.Canonical.CliffordHolonomyCurvature` | 8 | 0 |
| `InfoGeometry.OperatorAlgebra.ThermalBogoliubovCAR` | 27 | 0 |
| `InfoGeometry.OperatorAlgebra.ThreeZ2OperatorGradings` | 20 | 0 |
| `InfoGeometry.OperatorAlgebra.QuadraticNoncommutativeIdentity` | 30 | 0 |
| `InfoGeometry.OperatorAlgebra.InnerConjugation` | 32 | 0 |

### Imported warnings

Nine warnings occur in three imported owners outside the selected eleven. Each source was compared byte-for-byte to the base revision and is unchanged.

| Imported owner | Warnings | Disposition |
|---|---:|---|
| `InfoGeometry.Clifford.SplitQ11` | 1 | Existing deprecated `Mathlib.Data.Real.Basic` import at line 3. |
| `InfoGeometry.Clifford.SplitAtomDoubling` | 6 | Existing unused `Matrix.mul_apply` and `Fin.sum_univ_two` simp arguments at lines 71, 77, and 83. |
| `InfoGeometry.Geometry.AssociativeGaugeConnection` | 2 | Existing unused section-variable assumptions in `curvature_antisymm` and `cyclic_conjugate` at lines 57 and 121. |

These warnings were recorded, not suppressed. They do not change the zero-warning claim for the eleven selected owners.

### Dependency observation

The Mathlib checkout matches its exact pin and has no source diff. Its nested Batteries checkout is at the matching nested-manifest revision `f2effa3d803fda822b1f97b806c47cf2adfbcbc2`; its observed worktree difference is a type/content change only at `docs/README.md`. No Batteries Lean source change was observed. That pre-existing documentation change was preserved. This run freshly recompiles the repository closure against pinned prebuilt native imports; it is not a source rebuild of every dependency package.

## Static checks and dispositions

All eleven `placeholder_audit.py --root FILE --strict` invocations exited **0**: **0 hard, 11 soft, 0 advisory findings**. The soft findings are direct evaluations, specializations, or naturality lemmas:

| Soft finding | Disposition |
|---|---|
| `cube_zero` | Specializes the stronger proved mixed-triple-zero identity to three equal arguments. |
| `bch_neg` | Substitutes an additive negative into the independently defined BCH polynomial. |
| `coe_diagonalUnit_inv` | Evaluates the inverse field of the constructed native unit. |
| `spinor_curvature_eq_iff` | Derives the exact derivative-cancellation criterion from the preceding full curvature formula. |
| `RingHom.map_operatorThermalCreator` | Existing preservation of an ordered operator polynomial by a ring homomorphism. |
| `thermalAnnihilator_map` | Existing algebra-homomorphism compatibility in the explicitly scoped central-scalar specialization. |
| `thermalCreator_map` | Same explicitly scoped scalar specialization; the operator algebra remains noncommutative. |
| `RingHom.map_grandCanonicalOperator` | Existing ring-polynomial naturality theorem. |
| `RingHom.map_quadraticCommutator` | Existing preservation of subtraction and ordered multiplication. |
| `innerConjugation_idempotent_iff` | Existing specialization of the separately proved n-potent equivalence to exponent two. |
| `innerConjugationNat_zero` | Existing evaluation of conjugation by the zeroth unit power. |

The strict `semantic_vacuity_gate.py FILE... --fail-on warning` invocation exited **1** with **22 `trivial_surface` warnings, 0 errors**: 15 findings in new owners and 7 in existing owners. The scanner is a lexical heuristic. The following source review accepts each lemma in its actual API or derived-result role; no flagged lemma is a replacement for an unproved substantive claim.

| Flagged declaration | Independent source review |
|---|---|
| `coe_cayleyFactorUnit` | Evaluation of the value field of an explicitly constructed two-sided unit; the inverse laws are proved in the construction. |
| `coe_cayleyFactorUnit_inv` | Evaluation of the inverse field of that constructed unit; it exposes the ordered polynomial inverse. |
| `onePlusUnit_val` | Evaluation of the value field of the unit constructed from mixed nilpotence. |
| `onePlusUnit_inv_val` | Evaluation of its explicitly proved polynomial inverse; not an assumed invertibility statement. |
| `bch_neg` | Substitution into the independently defined BCH polynomial; the commutator with the additive negative cancels. |
| `expEquiv_unit` | Identifies the explicitly composed coordinate equivalence with its separately named exponential unit. |
| `expMulEquiv_unit` | Identifies the multiplicative equivalence value; substantive BCH compatibility is proved separately by expUnit_mul and toStrict_mul. |
| `spinor_curvature_eq_iff` | Cancellation criterion derived from the preceding full derivative-correction formula; separate derivative vanishing is not assumed necessary. |
| `adjointCovariantDerivative_apply` | Evaluation of the native linear endomorphism sum; its curvature and Leibniz behavior are established by separate theorems. |
| `innerConjugationRingEquiv_apply` | Existing evaluation lemma for the independently constructed ring equivalence. |
| `innerConjugationNat_zero` | Existing evaluation of conjugation by the zeroth power of a unit. |
| `RingHom.map_grandCanonicalOperator` | Existing naturality under an arbitrary ring homomorphism, using preservation of the actual ordered ring polynomial. |
| `RingHom.map_quadraticCommutator` | Existing ring-homomorphism preservation of subtraction and ordered multiplication. |
| `RingHom.map_operatorThermalCreator` | Existing preservation of the ordered operator polynomial by an arbitrary ring homomorphism. |
| `thermalAnnihilator_map` | Existing algebra-homomorphism compatibility with the explicitly central scalar specialization; it does not impose commutativity on the operator algebra. |
| `thermalCreator_map` | Existing algebra-homomorphism compatibility with the same explicitly scoped scalar specialization. |
| `coe_diagonalUnit` | Evaluation of the native diagonal homomorphism lifted to units. |
| `coe_diagonalUnit_inv` | Evaluation of the inverse of an actual diagonal unit; no additional matrix-invertibility hypothesis. |
| `coe_permutationUnit` | Evaluation of the permutation unit constructed with its two inverse laws. |
| `coe_permutationUnit_inv` | Evaluation of the inverse permutation unit; the convention is fixed by the entry theorem. |
| `coe_weightedShift` | Evaluation of the product of the diagonal and permutation units. |
| `coe_weightedShift_inv` | Evaluation of the inverse product with reversed order; the explicit weighted-shift inverse theorem is proved separately. |

## Mathematical acceptance

The strict-upper owner constructs a full native `NonUnitalSubring`, not a property supplied by a wrapper. All mixed triple products vanish, which supports the integral polynomial inverse and ordered group commutator. The native unitriangular `Subgroup` and `shiftEquiv` identify exactly the matrices of the form `1 + X`. The named native matrices `root01` and `root12` both have proved membership in this subring, and their products differ in entry `(0,2)` under `Nontrivial A`. The witness therefore establishes genuine noncommutativity of the intended carrier.

The BCH owner requires only invertibility of two beyond the ring assumptions. Its exponential and logarithm are explicit finite polynomials. The exponential bijection is used to transport a group structure to a separate coordinate type, and `toStrict_mul` independently identifies that multiplication with `X + Y + half (X*Y - Y*X)`. It does not identify ordinary addition with the unitriangular group or assert an analytic exponential theorem.

The quaternion and nested-matrix owners prove ordered multiplication, anticommutation, square, and commutator identities in arbitrary rings. Integer-specialized rotor reuse preserves arbitrary operator coefficients. Integral sandwiches are separated from invertible-two normalized units. Strict noncommutation additionally requires nontriviality. No compactness, linear independence, arbitrary-ring Clifford classification, or Lie-closed coefficient span is inferred.

Weighted permutation matrices are constructed as actual units from native diagonal and permutation maps. The row-`i`, column-`sigma(i)` convention agrees with the ordered holonomy, inverse shift, global commutator, endpoint gauge transform, and matrix conjugation identities. The generic group layer does not require a finite index type; the matrix realization explicitly does. No categorical braiding, Yang--Baxter relation, or continuum map is asserted.

The adjoint connection is a native linear endomorphism built from the existing inner derivative. Ordered Leibniz expansion proves the complete base-commutator defects. Pairwise commuting base operators yield element-valued cyclic Bianchi even for zero or dependent directions and arbitrary independent potentials. This proof does not infer an element is zero merely from vanishing of its inner derivation. The curvature-square expansion retains both ordered mixed terms.

The canonical bridge uses the actual nested quaternion matrices as potentials. `spinor_curvature_formula` retains the derivative difference; `spinor_curvature_eq_iff` gives the exact cancellation criterion. Separate annihilation hypotheses are documented as sufficient. Zero derivations supply an explicit realization, and the existing gauge-covariance owner transports it by units of the full nested matrix ring. The value `2 * thirdAxis` is not asserted nonzero in characteristic two. No unsupported bridge from BCH or discrete holonomy to differential geometry is added.

The constant-axis necessity wording identified in preflight is corrected in the committed contract. The outer matrix dimensions are explicit; the coefficient ring may itself be an endomorphism ring without a finite-dimensional underlying module assumption.

## Review of import-maintained owners

Compared with the base revision, the four existing owners have unchanged declaration statements. After removing only import lines and the added leading copyright header, their bodies agree exactly with the base, except for removal of the single unused `add_comm` simp argument in `ThermalBogoliubovCAR.thermalAnticommutator_expand`.

The narrowed imports preserve the existing `FiniteSpinAlgebra` dependency. `InnerConjugation` explicitly imports `Mathlib.Algebra.Polynomial.AlgebraMap` for its integer-polynomial evaluation API. All 109 declarations owned by these four modules were included in the fresh native audit and all four compiled with zero warnings. No gate implementation or dependency pin was changed to obtain acceptance.

## Workflow review

The dedicated workflow selects all eleven audited targets, reads the exact dependency pin, fetches the exact requested project revision, preserves readonly repository permissions, obtains native import artifacts under the shared lock, and invokes the maintained source checker. It explicitly checks zero warnings for every selected owner. It runs strict placeholder scans and records semantic findings with an error-severity failure threshold. This local acceptance additionally used the stricter warning threshold and records its nonzero result above. The artifact-upload step retains the native report, source hashes, generated audit source, compiler/audit logs, and semantic report.

Workflow source inspection is not a claim that remote CI has run successfully. Root-workspace integration, publication gates, and remote checks remain separate responsibilities.

## Source hashes

The full 22-module source closure, dependency graph, fingerprints, native artifact hashes, and verifier hashes are in the checker report. The selected-owner source hashes are:

| Reviewed owner | SHA-256 |
|---|---|
| `InfoGeometry.Algebra.StrictUpper3` | `0bf219fb012d4254625b4cd82115ed0793a06efe2539563dc48970cfb531c526` |
| `InfoGeometry.Algebra.StrictUpperBCH3` | `36dcd293e932128b0145250a63675a1d5c7e31bd6bfc9366d2d1aaad566196e9` |
| `InfoGeometry.Algebra.QuaternionCayleyPair` | `62a62710400c49736cf18ba68943231d6478957d6f9ec13ef9cb3a2ca1db6371` |
| `InfoGeometry.Clifford.SplitAtomQuaternion` | `8b3b01538a569374dc547ccdc072488437f35de40169b6a66f788edce696190c` |
| `InfoGeometry.Geometry.AssociativeBianchi` | `c794ea38c63de886468a00e0f5fcc800c8a9603266cb146988ceface3ca28b14` |
| `InfoGeometry.OperatorAlgebra.WeightedPermutationHolonomy` | `52bbf73db89ebeba4209133e57471f85cb603b68b2f3f5f222028a6f0bb4614e` |
| `InfoGeometry.Canonical.CliffordHolonomyCurvature` | `3f38f1ae83b73122bbe34a05e9fbe22a835a8df879666a51bf29fe86ad9328fe` |
| `InfoGeometry.OperatorAlgebra.ThermalBogoliubovCAR` | `6214daf3dd3c7943566958fa6237b08f986bad330a89ed5c3b7b08a51af93dce` |
| `InfoGeometry.OperatorAlgebra.ThreeZ2OperatorGradings` | `c2a4373b4a27cddf3a7b176582180e719c9286c89dd632dce6bec530118809a6` |
| `InfoGeometry.OperatorAlgebra.QuadraticNoncommutativeIdentity` | `7a6e81146d8056c560c20885226d1b89856cb4fdb7e3ba9d1884dc64796e9f97` |
| `InfoGeometry.OperatorAlgebra.InnerConjugation` | `ad4d4c83ff3e2f011d45cf25a89db9445d166245d97a36d597161c4a9fb4af80` |

## Reproduction and evidence

The successful native command was:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/66380c6bf432/info-geometry-lean/.lake/packages/mathlib \
  --lean /workspace/scratch/4796737fb777/lean-environment/lean-4.34.1-linux/bin/lean \
  --target InfoGeometry.Algebra.StrictUpper3 \
  --target InfoGeometry.Algebra.StrictUpperBCH3 \
  --target InfoGeometry.Algebra.QuaternionCayleyPair \
  --target InfoGeometry.Clifford.SplitAtomQuaternion \
  --target InfoGeometry.Geometry.AssociativeBianchi \
  --target InfoGeometry.OperatorAlgebra.WeightedPermutationHolonomy \
  --target InfoGeometry.Canonical.CliffordHolonomyCurvature \
  --target InfoGeometry.OperatorAlgebra.ThermalBogoliubovCAR \
  --target InfoGeometry.OperatorAlgebra.ThreeZ2OperatorGradings \
  --target InfoGeometry.OperatorAlgebra.QuadraticNoncommutativeIdentity \
  --target InfoGeometry.OperatorAlgebra.InnerConjugation \
  --output /workspace/scratch/d18a558d1d7d/chain-qa-final
```

Run `python3 tools/quality/placeholder_audit.py --root FILE --strict` once per selected owner, then `python3 tools/quality/semantic_vacuity_gate.py FILE... --fail-on warning`. The exact static commands, exit codes, raw outputs, hashes, old-owner body comparison, and imported-warning source comparison are preserved in `static-gates.json`. Individual placeholder JSON files and the full `semantic.json` are in the same review directory.

Native evidence is in `/workspace/scratch/d18a558d1d7d/chain-qa-final`: `report.json`, `axioms.log`, `evidence-sha256.json`, `src/CliffordDiracAudit.lean`, and per-module logs. This independent review and static evidence are in `/workspace/scratch/d18a558d1d7d/chain-qa-review`.

## Remaining scope

`InfoGeometry.Canonical.All` was not compiled by this review. No full root project, all-default-targets, external-package initialization, pre-push gate, or remote CI success is claimed. The kernel-certified conclusions above are tied to the selected source closure and exact source hashes. This reviewer did not modify or commit repository source.

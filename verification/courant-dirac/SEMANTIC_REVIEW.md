# Independent semantic/source review

## Verdict and validation boundary

**PASS — source and mathematical-scope review only.**

An independent read-only reviewer inspected the owners listed below and the
relevant repository/Mathlib definitions before an execution-environment reset,
then re-read all four restored owners and the reconstructed contract, followed
by the narrow native-class packaging changes, capstone import routing, and
mechanical graph and matrix proof repairs. No
required semantic changes were found in the reviewed versions. The reviewer
did not author or edit theorem content, compile Lean, run Lake, or acquire the
shared build lock.

**Compilation and declaration-axiom validation remain pending in this record.**
This report preserves the historical reviews and the fresh restored-source
review below. The initial restoration matched three historical owner hashes;
the subsequent Lie, graph, and matrix proof repairs were independently re-reviewed.
The current source-review
verdict applies to the hashes in the latest review table, as amended by any
explicit reconciliation addendum below. Later edits require
hash reconciliation or review of differences. A separate validation receipt
may record compilation; the source-review verdict does not establish it.

The original uploaded attachment is not currently available as local bytes.
Its mathematical content was inspected before the reset; this report makes
no attachment checksum or byte-preservation claim.

## First review: generic owners and theorem contract

The following source-level evidence was checked. Line numbers refer to the
versions reviewed at that stage, before the later matrix-obstruction additions.

| Surface | Source evidence | Finding |
|---|---|---|
| Carrier and neutral normalization | `NeutralPhaseSpaceCore.lean:36`, `:61`; `CotangentLieAlgebra.lean:39`; `SkewGraphNeutralPairing.lean:34` | Primal-first `E × Module.Dual ℝ E` and `B((x,ξ),(y,η)) = ξ(y) + η(x)` are used consistently |
| Cotangent Lie algebra | `CotangentLieAlgebra.lean:79`, `:91`, `:100` | Native coadjoint Lie-module identities supply Jacobi; explicit named structures avoid global product-instance conflicts |
| Neutral invariance | `CotangentLieAlgebra.lean:106` | Coadjoint signs match the existing neutral form; the cancellation is correct |
| Hemi-semidirect operation | `CotangentLieAlgebra.lean:132`, `:151`, `:160`, `:168`, `:179`, `:189` | Left Leibniz, symmetric sum, pairing invariance, nonzero witnesses, and the abelianity characterization are consistent |
| Unit models and KKS sign | `CotangentUnitLinearization.lean:40`, `:48`, `:52`; `SouriauKKSForm.lean:20` | `poissonSharp α X = -⁅X,α⁆` evaluates to `α ⁅X,Y⁆`, matching the existing KKS convention |
| Kernel/stabilizer identification | `CotangentUnitLinearization.lean:65`, `:78`, `:131` | Accurate algebraic equivalences; no automatic entropy interpretation |
| Differential scope | `CotangentUnitLinearization.lean:24`; original `THEOREM_CONTRACT.md:21`, `:61` | Actual smooth source/target derivative identification remains outside the proved scope |
| Isotropy and maximality | `SkewGraphNeutralPairing.lean:54`, `:68` | Evaluation-skewness is the correct criterion; the orthogonal equality explicitly uses dual separation |
| Cross-pairing | `SkewGraphNeutralPairing.lean:97` | Sign and factor two match the neutral normalization |
| Intersection and splitting | `SkewGraphNeutralPairing.lean:107`, `:128`, `:140`, `:157`, `:189` | Intersection has no skewness assumption; injectivity, surjectivity, and bijectivity have their proper distinct roles |
| Scope and naming | Original `THEOREM_CONTRACT.md:19`, `:32`, `:61` | Contract separates cotangent Lie algebra, zero-cobracket interpretation, algebraic graphs, and unproved manifold/Courant claims |

The reviewer checked the cotangent Jacobi cancellation, graph-orthogonal
orientation, intersection's factor-of-two argument, and explicit graph-sum
construction. No semantic error or vacuous hypothesis trick was found.

### First-review hashes

| File | SHA-256 |
|---|---|
| `lean/InfoGeometry/Lie/CotangentLieAlgebra.lean` | `830bfbf9ed7793510d306a8d30b4d6dea0cc4e30299956ed086354baa7199f55` |
| `lean/InfoGeometry/Geometry/CotangentUnitLinearization.lean` | `1faf046b416e15d1acf6fffd7fadc7ebdbb9b4030c6ca64e63d92390ab23ac07` |
| `lean/InfoGeometry/Geometry/SkewGraphNeutralPairing.lean` | `a1827a58b4f42723bd1ad8ec05ed2bffb97c64f7c5fafa45727fb14e178add96` |
| Original `verification/courant-dirac/THEOREM_CONTRACT.md` | `53fc026a2271127310bf8b0393e0934d5c3b9a8fbcbd79dd9c2378c4fc5275ae` |

The contract hash above belongs to the original reviewed document. The current
reconstructed contract intentionally adds reset/provenance qualifications and
the later explicit matrix witness; it is not expected to have that hash.

## Second review: finite matrix adapter and explicit obstruction

**PASS — no required semantic corrections found.**

### Coordinate transport

`MatrixDiracGraphs.lean:32` defines the dual-to-primal map by composing
`Matrix.toLin' P` with the inverse of `dotProductEquiv`. The equivalence at
line 37 changes only the second phase-space coordinate. The formulas therefore
transport the actual neutral pairing and actual graph submodules; they do not
introduce an implicit primal/dual identification.

| Claim | Source evidence |
|---|---|
| Coordinate-neutral pairing compatibility | `MatrixDiracGraphs.lean:54` |
| Evaluation-skewness iff matrix transpose equals the negative | `MatrixDiracGraphs.lean:64` |
| Graph membership agrees with `u = P *ᵥ ξ` | `MatrixDiracGraphs.lean:86` |
| Graph isotropy iff matrix skewness | `MatrixDiracGraphs.lean:98`, `:104` |
| Skew graph equals its neutral orthogonal | `MatrixDiracGraphs.lean:126` |
| Opposite graph isotropy | `MatrixDiracGraphs.lean:132` |
| Cross-pairing equals `2 * dotProduct (P *ᵥ a) b` | `MatrixDiracGraphs.lean:143` |
| Intersection equals zero primal coordinate over the matrix kernel, without skewness | `MatrixDiracGraphs.lean:154` |

The finite-index hypotheses include every `Fin n`, including the empty case.
The adapter uses full finite matrices and records its fiberwise linear-algebra
scope. No scalar, diagonal, or commuting replacement is made.

The reviewer inspected the following native Mathlib source definitions in the
validation source tree:

- `Mathlib/LinearAlgebra/Matrix/Dual.lean:49`: `dotProductEquiv` sends a vector
  `v` to the covector `w ↦ dotProduct v w`.
- `Mathlib/Data/Matrix/Mul.lean:1108`: the transpose-pairing identity has the
  orientation used by the adapter.
- `Mathlib/LinearAlgebra/SesquilinearForm/Orthogonal.lean:54`: the orthogonal
  membership convention agrees with the generic graph proof.

### Concrete obstruction

The appended `MatrixObstruction` section uses the existing full real matrix
algebra `Mat2R = Matrix (Fin 2) (Fin 2) ℝ`, with its native associative
commutator Lie structure (`CotangentLieAlgebra.lean:215` in the second-reviewed
version). The chosen matrices and covector are

```text
H = E₀₀
E = E₀₁
α(A) = A₀₁.
```

Ordinary matrix multiplication gives `H * E = E` and `E * H = 0`. Hence
`⁅H,E⁆ = E` and `α ⁅H,E⁆ = 1`. The symmetric sum of the hemi-semidirect
operation on `(H,0)` and `(0,α)`, evaluated at `E`, is exactly `-1`.
`matrix_hemi_symmetric_sum_eq_neg_one` records that fact at line 242.

The proposed neutral-pairing derivative is zero by the previously proved
invariance theorem. `matrix_hemi_pairing_derivative_identity_fails`, at line
251, compares those same two quantities and establishes their inequality.
Acting by `(E,0)` through the hemi operation is exactly the diagonal
adjoint/coadjoint action needed for this comparison. The counterexample uses
an actual algebraic covector and no additional nonvanishing assumption.

The relevant native Mathlib conventions were checked in:

- `Mathlib/Algebra/Lie/OfAssociative.lean:57`: associative bracket `x*y - y*x`.
- `Mathlib/Algebra/Lie/Basic.lean:294`: coadjoint evaluation `-α ⁅x,m⁆`.
- `Mathlib/Data/Matrix/Basis.lean:331`, `:346`: matrix-unit multiplication.

### Second-review hashes

| File | SHA-256 |
|---|---|
| `lean/InfoGeometry/Geometry/MatrixDiracGraphs.lean` | `f421eed87480b01d5698bf44b2fe6fd05ea21942cda7b7d59c91bb7fac88b2b0` |
| `lean/InfoGeometry/Lie/CotangentLieAlgebra.lean`, including the matrix obstruction | `c578b08d6d7f114ac2230d7ea10e1b773e9f8f2075b89c3431e7f169601ab78d` |

## Third review: restored sources and Lie elaboration repairs

**PASS — source reconciliation and independent semantic re-review.**

The reviewer re-read all four integrated owners and the reconstructed contract
under `/workspace/scratch/3288f93e1961/info-geometry-lean`. The unit, generic
graph, and matrix adapter files match their earlier reviewed SHA-256 hashes.
Their carriers, definitions, theorem statements, assumptions, and scope
boundaries remain as described above. The integrated contract matches the
reconstructed candidate and accurately records the matrix witness and the
limits of the algebraic results.

The revised Lie owner retains the same bracket definitions, hypotheses,
theorem statements, neutral normalization, and concrete obstruction. Its
changes are proof elaboration and API disambiguation:

| Changed surface | Current source evidence | Semantic finding |
|---|---|---|
| Scalar compatibility proofs | `CotangentLieAlgebra.lean:62`, `:70` | Explicit `LieModule.smul_lie` and `LieModule.lie_smul` replace broad simplification; these are the same native real Lie-module laws |
| Inherited additive/module structures | `CotangentLieAlgebra.lean:102`, `:111` | Annotated `inferInstance` terms select the existing additive group and module; the constructed cotangent bracket and scalar multiplication are unchanged |
| Matrix readout | `CotangentLieAlgebra.lean:232` | Typed projection maps still read exactly `A 0 1`; no different covector or carrier is introduced |
| Minus-one witness | `CotangentLieAlgebra.lean:251` | Narrow simplification uses the established readout-of-commutator identity and zero evaluation; the exact `-1` result is unchanged |
| Zero derivative expression | `CotangentLieAlgebra.lean:271` | Negating the existing pairing-invariance equality replaces arithmetic automation; it proves the same right-hand side is zero |

No theorem weakening, additional mathematical assumption, replacement of the
native coadjoint representation, or loss of noncommutative matrix content was
found. The prior semantic PASS therefore extends to this revised source
version. The reviewer did not inspect a completed build receipt or run a
compiler, so compilation and declaration-axiom acceptance remain pending in
this report.

### Third-review hashes

| File | SHA-256 |
|---|---|
| `lean/InfoGeometry/Lie/CotangentLieAlgebra.lean` | `e6fd4eec6135ea066c289e49df9301813deb8f1726101ef5dcee262b67705a73` |
| `lean/InfoGeometry/Geometry/CotangentUnitLinearization.lean` | `1faf046b416e15d1acf6fffd7fadc7ebdbb9b4030c6ca64e63d92390ab23ac07` |
| `lean/InfoGeometry/Geometry/SkewGraphNeutralPairing.lean` | `a1827a58b4f42723bd1ad8ec05ed2bffb97c64f7c5fafa45727fb14e178add96` |
| `lean/InfoGeometry/Geometry/MatrixDiracGraphs.lean` | `f421eed87480b01d5698bf44b2fe6fd05ea21942cda7b7d59c91bb7fac88b2b0` |
| `verification/courant-dirac/THEOREM_CONTRACT.md` | `9d47faa64f126e22e6a727beff43513259fb5b468c921cc8da9defb33d90ad0e` |

## Fourth review: native class packaging and capstone import routing

**PASS — narrow semantic reconciliation; no change to mathematical claims.**

The cotangent owner now marks its two named class definitions with
`@[instance_reducible]` and constructs `cotangentLieAlgebra` under a local
`letI : LieRing (PhaseSpaceCarrier g) := cotangentLieRing`. Its declared type
still fixes exactly that cotangent Lie ring, and the scalar compatibility
proof is still `cotangentBracket_smul_right`.

These changes resolve class elaboration without changing the bracket,
underlying additive group, scalar multiplication, hypotheses, or theorem
statements. `instance_reducible` is not a global instance declaration: the
definitions remain explicit named structures, and the local instance is
confined to the construction. The scope statement about avoiding competing
global product instances remains accurate.

The reviewer inspected the exact source diff and the relevant construction
at `CotangentLieAlgebra.lean:102` and `:111`. No semantic concern was found.

The capstone at
`lean/InfoGeometry/Geometry/CourantDrinfeldDiracCapstone.lean` imports the four
reviewed owners at lines 6–9 and contains only a scope-qualified module
comment. It introduces no new theorem, assumption, or global class instance.
`lean/InfoGeometry/All.lean:6` adds one import of that capstone. The existing
root `lean/InfoGeometry.lean:1338` already imports `InfoGeometry.All`.

`git diff HEAD` over `All.lean`, `InfoGeometry.lean`, and
`AllExhaustive.lean` showed only the single capstone import addition in
`All.lean`. This review establishes the intended source import routing; it
does not certify a build of either large umbrella module.

### Fourth-review hashes

| File | SHA-256 |
|---|---|
| `lean/InfoGeometry/Lie/CotangentLieAlgebra.lean` | `39f7acaad523ee81a798ccbc8de7eb295b25c369bdc1ab6c63b3b18d6b4530fe` |
| `lean/InfoGeometry/Geometry/CotangentUnitLinearization.lean` | `1faf046b416e15d1acf6fffd7fadc7ebdbb9b4030c6ca64e63d92390ab23ac07` |
| `lean/InfoGeometry/Geometry/SkewGraphNeutralPairing.lean` | `a1827a58b4f42723bd1ad8ec05ed2bffb97c64f7c5fafa45727fb14e178add96` |
| `lean/InfoGeometry/Geometry/MatrixDiracGraphs.lean` | `f421eed87480b01d5698bf44b2fe6fd05ea21942cda7b7d59c91bb7fac88b2b0` |
| `lean/InfoGeometry/Geometry/CourantDrinfeldDiracCapstone.lean` | `5ce030234bffcec556f72cc8ff818b78e7562d938165be34ed621fe6f8a2701e` |
| `lean/InfoGeometry/All.lean` | `40f206eafd48dac9b2c036abf6bb8661cf5991dc02a6342e4b597ae8682abfaa` |
| Unchanged `lean/InfoGeometry.lean` | `db6ab6074efbd123b976979988edd993403898741f989c9e8de58964e5d3a523` |
| `verification/courant-dirac/THEOREM_CONTRACT.md` | `9d47faa64f126e22e6a727beff43513259fb5b468c921cc8da9defb33d90ad0e` |

No compiler was invoked by this reviewer. Final compilation, axiom audit,
and repository-gate results remain the responsibility of the separate
acceptance record; this PASS concerns source semantics and import routing.

## Fifth review: graph linearity rewrites and local witness names

**PASS — mechanical proof repair; statements and constructions unchanged.**

The reviewer inspected the current graph owner's full source and its diff
against the index. Only two explicit linearity rewrites and the local names
of the two decomposition witnesses changed.

- `SkewGraphNeutralPairing.lean:82` now rewrites `map_sub` before simplifying
  the orthogonality consequence. It proves the same equality
  `ξ (z.1 - P z.2) = 0` from the same neutral-pairing equation and skewness
  hypothesis.
- `SkewGraphNeutralPairing.lean:170` likewise rewrites `map_sub` before
  simplifying the primal coordinate of a sum of opposite graph vectors. It
  still supplies `z.2 - w.2` as the preimage proving surjectivity.
- The two local witnesses at lines 177–178 are now called `ξplus` and
  `ξminus`. Their values remain exactly `(1/2) • (z.2 + η)` and
  `(1/2) • (z.2 - η)`, and all subsequent references were renamed consistently.

The graph map, neutral form, all theorem statements and hypotheses, and the
intersection/complementarity criteria are unchanged. Both explicit rewrites
are the linearity identities required by the existing argument. No semantic
concern or additional proof assumption was found.

This source review does not claim that the cited compiler failures were
reproduced or that the repairs have passed compilation; no compiler was run
by the reviewer. The parent owns compiler receipts and final acceptance gates.

### Fifth-review hashes

| File | SHA-256 |
|---|---|
| `lean/InfoGeometry/Lie/CotangentLieAlgebra.lean` | `39f7acaad523ee81a798ccbc8de7eb295b25c369bdc1ab6c63b3b18d6b4530fe` |
| `lean/InfoGeometry/Geometry/CotangentUnitLinearization.lean` | `1faf046b416e15d1acf6fffd7fadc7ebdbb9b4030c6ca64e63d92390ab23ac07` |
| `lean/InfoGeometry/Geometry/SkewGraphNeutralPairing.lean` | `3e823559b3be812646619c60a2dcdc40c2e2f2de90f7b5ef545c8c0d1fc5b246` |
| `lean/InfoGeometry/Geometry/MatrixDiracGraphs.lean` | `f421eed87480b01d5698bf44b2fe6fd05ea21942cda7b7d59c91bb7fac88b2b0` |
| `lean/InfoGeometry/Geometry/CourantDrinfeldDiracCapstone.lean` | `5ce030234bffcec556f72cc8ff818b78e7562d938165be34ed621fe6f8a2701e` |
| `lean/InfoGeometry/All.lean` | `40f206eafd48dac9b2c036abf6bb8661cf5991dc02a6342e4b597ae8682abfaa` |
| `verification/courant-dirac/THEOREM_CONTRACT.md` | `9d47faa64f126e22e6a727beff43513259fb5b468c921cc8da9defb33d90ad0e` |

## Sixth review: matrix proof elaboration repairs

**PASS — three proof-script repairs; no statement, hypothesis, or import changes.**

The reviewer inspected the complete current `MatrixDiracGraphs.lean`. As an
additional exact comparison, the three reported edits were reversed in memory
without writing any theorem file. The resulting text had SHA-256
`f421eed87480b01d5698bf44b2fe6fd05ea21942cda7b7d59c91bb7fac88b2b0`, exactly
the previously reviewed matrix source. This confirms that the three proof
fragments below are the entire difference from that reviewed version.

| Repair | Current source evidence | Semantic finding |
|---|---|---|
| Product-application simplification | `MatrixDiracGraphs.lean:117` | `Function.prod_apply` replaces `LinearMap.prod_apply` when expanding the same range representative; the graph vector and surjective coordinate transport are unchanged |
| Cross-pair evaluation | `MatrixDiracGraphs.lean:150` | The generic cross-pair theorem is simplified first, and `change` exposes `(dotProductEquiv ℝ ι b) (P *ᵥ a)` as `dotProduct b (P *ᵥ a)`; dot-product commutativity then gives the same declared factor-two formula |
| Intersection transport | `MatrixDiracGraphs.lean:162` | Generic `mem_dualGraph`, followed by coordinate and negation evaluation, replaces coordinate-specific rewrite lemmas; the same unconditional kernel-intersection equivalence is obtained |

All three changes preserve the actual algebraic dual, primal-first carrier,
neutral normalization, arbitrary finite index type, and full matrix map.
There is no new assumption, weakened conclusion, altered sign, or scalar
replacement. The source-review PASS extends to the hash below.

No Lean or Lake command was run by the reviewer. Reported compilation results
for individual owners and the running matrix compilation are not promoted by
this source receipt to final compiler or axiom acceptance. Those results belong
in the parent's separate validation record.

### Sixth-review hashes

| File | SHA-256 |
|---|---|
| `lean/InfoGeometry/Lie/CotangentLieAlgebra.lean` | `39f7acaad523ee81a798ccbc8de7eb295b25c369bdc1ab6c63b3b18d6b4530fe` |
| `lean/InfoGeometry/Geometry/CotangentUnitLinearization.lean` | `1faf046b416e15d1acf6fffd7fadc7ebdbb9b4030c6ca64e63d92390ab23ac07` |
| `lean/InfoGeometry/Geometry/SkewGraphNeutralPairing.lean` | `3e823559b3be812646619c60a2dcdc40c2e2f2de90f7b5ef545c8c0d1fc5b246` |
| `lean/InfoGeometry/Geometry/MatrixDiracGraphs.lean` | `6779b184815e259dadf6a88ba30686428766cebac7798998af84e0319c87b2cd` |
| `lean/InfoGeometry/Geometry/CourantDrinfeldDiracCapstone.lean` | `5ce030234bffcec556f72cc8ff818b78e7562d938165be34ed621fe6f8a2701e` |
| `lean/InfoGeometry/All.lean` | `40f206eafd48dac9b2c036abf6bb8661cf5991dc02a6342e4b597ae8682abfaa` |
| `verification/courant-dirac/THEOREM_CONTRACT.md` | `9d47faa64f126e22e6a727beff43513259fb5b468c921cc8da9defb33d90ad0e` |

### Final matrix proof reconciliation

**PASS.** At `MatrixDiracGraphs.lean:117`, the simplification list now includes
both `LinearMap.prod_apply` and `Function.prod_apply`, in that order. These
expand successive definitional layers of the same product-map application;
no carrier, witness, statement, or assumption changes. Reversing only this
added simplification lemma in memory reproduces the sixth-review matrix hash
`6779b184815e259dadf6a88ba30686428766cebac7798998af84e0319c87b2cd` exactly.

The current matrix source hash is
`07fe9bfc4410845f7a763afc40cdda884a85a590230128e5ed4e91b6d03230d8`,
superseding the matrix entry in the sixth-review table. All other reviewed
hashes remain as recorded. This is source reconciliation only; the reviewer
ran no compiler and acquired no build lock.

## Checks performed and remaining gates

The original read-only checks consisted of line-numbered source inspection,
inspection of the reused definitions, `git status --short`, `sha256sum`, and
a text scan of the relevant owners. The restored-source review repeated
source inspection and hashing for all four owners and the contract and
repeated the text scan for all four owners. The scans found no occurrences of
`sorry`, `admit`, declaration-level `axiom`, `native_decide`, `unsafe`, or
`Prop := True`. A text scan is not a declaration-axiom audit.

Outstanding acceptance work:

1. Keep delivered source contents reconciled against the latest reviewed
   hashes above; independently review subsequent differences, including any
   further compiler repairs.
2. Compile the full sources at the pinned Lean/Mathlib versions, with warnings
   treated as errors.
3. Audit declaration axiom dependencies, including generated declarations.
4. Run the required repository proof/build gates at their stated narrow scope.
5. Record current validation commands, outputs, source hashes, and limitations
   separately from this historical source-review receipt.

This report does not claim a whole-repository build, smooth groupoid
formalization, Courant integrability theorem, general Lie bialgebra double,
or entropy-Casimir identification.

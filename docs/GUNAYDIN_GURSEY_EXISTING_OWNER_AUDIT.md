# Günaydin–Gürsey: existing-owner mathematical and CAS audit

Date: 2026-10-24. Lean v4.34.1. This is an audit of a bounded owner slice,
not authentication of the 1973 paper or a repository-wide certification.
No existing Lean owner was edited by this audit. Concurrent owner changes
were preserved and rechecked; the final CAS receipt pins the source hashes.

## Result

The existing Zorn derivation, Clifford and algebraic triality mathematics
passes the exact checks below. The proposed replacement in the conversation
has false off-diagonal signs and a false commutator normalization.

Final verification of twelve selected modules:

* Final locked twelve-owner build succeeded: **9,047 jobs**.
* All twelve modules, **1,262 declarations**, pass kernel replay and the
  transitive axiom allowlist (`propext`, `Classical.choice`, `Quot.sound`).
* Initially three export/replay modules failed the allowlist because of
  `native_decide` axioms. Concurrent repairs replaced those proofs with
  `decide +kernel`; this audit independently rebuilt and re-audited all twelve
  modules after the repairs. No false table entry was detected.
* Two final complete CAS runs produced bit-for-bit identical JSON; every
  recorded source hash matched at completion.
* Builds have existing dependency/linter warnings; no globally warning-free
  claim is made.

## Observed in repo-owned source

All paths in this table are relative to `lean/InfoGeometry/`.

| Owner | Actual checked scope | Axiom replay |
|---|---|---:|
| `Algebra/ZornVectorMatrix.lean` | Existing nonassociative product, norm, alternativity and linear derivation carrier | PASS: 524 |
| `Algebra/AlternativeDerivations.lean` | Generic linear derivations, polarized alternative laws and standard derivation machinery | PASS: 81 |
| `Algebra/Zorn/OffDiagonalDerivation.lean` | Correct six-parameter action over arbitrary commutative rings, upper/lower full-operator brackets, injectivity, quadratic norm variation | PASS: 15 |
| `Lie/CanonicalZornDerivationDimension.lean` | `parameterLinearEquiv`, `finrank_vectorDerivations`, `finrank_canonicalZornDerivations`: real derivations have dimension 14 | PASS: 59 |
| `Lie/CanonicalZornPeirceSL3Bridge.lean` | `peirceStabilizerEquivSL3` and separate `stabilizerMatrixSL3_lie`: actual stabilizer classification, not just one inclusion | PASS: 40 |
| `Lie/SplitOctonionCliffordAction.lean` | Native Clifford lift into endomorphisms; `leftCliffordQuadratic_eq_neg_det`, generator square and anticommutator | PASS: 30 |
| `Exceptional/CompositionTriality.lean` | Linear related triples for arbitrary bilinear multiplication; componentwise commutator and Lie algebra instances | PASS: 98 |
| `Exceptional/CompositionTrialityAlternativeBridge.lean` | Diagonal nonassociative derivations and bracket compatibility | PASS: 14 |
| `Lie/CanonicalZornG2CASData.lean` | Literal rational basis and structure constants | PASS: 5 |
| `Lie/CanonicalZornG2NativeMatrixExport.lean` | Rational parameter action and circular-frame export | PASS: 121 |
| `Lie/CanonicalZornG2BasisAlignment.lean` | Signed permutation connecting CAS and native generator orders | PASS: 72 |
| `Lie/CanonicalZornG2CASReplay.lean` | Replay of all stored bracket expansions | PASS: 203 |

The stabilizer equivalence is an ordinary equivalence with separate linearity
and bracket theorems; do not describe it as an already bundled `LieEquiv`.
The dimension/classification owners above use **ℝ**, not all commutative rings.

`Lie/All.lean` imports the classification, stabilizer and Clifford owners;
`InfoGeometry/All.lean` directly imports the stabilizer bridge and its audit.
The generic triality owner does not assume alternativity: closure follows
from linearity and bilinearity alone.

The older `Lie/ZornPeirceDerivationStabilizer.lean` says that *it* does not
identify the stabilizer with sl3. That local statement must not be promoted
to a codebase-wide gap: `CanonicalZornPeirceSL3Bridge.lean` supplies the
classification.

## Computer algebra: actual definitions, not a guessed basis

Generator: `scratch/cas/gunaydin_gursey_existing_owners.py`.
Receipt: `docs/GUNAYDIN_GURSEY_EXISTING_OWNER_CAS.json`.
Engines: SymPy 1.14.0 and independent Sage 10.9 rational linear algebra.

The audit reuses:

* `tools/sympy/split_octonion_multiplication.py`;
* `tools/sympy/split_octonion_derivation_classification.py` (its exact
  constraint constructor, not unrelated optional floating-point checks).

It parses the actual Lean `parameterAction`, `rationalParameterAction`,
`offDiagonalAction`, literal circular matrices, CAS basis, signed change of
basis, and structure constants using a restricted arithmetic reader.
Unsupported syntax fails rather than being guessed. The Zorn multiplication
translation was manually aligned with `Algebra/ZornVectorMatrix.mul`.
Hashes identify all participating source snapshots.

Frozen CAS basis: `(E11,E22,U0,U1,U2,V0,V1,V2)`.
Native matrix readout: `(a,upper0,upper1,upper2,b,lower0,lower1,lower2)`.
Matrices act on columns; `AB` means apply `B`, then `A`. The audit explicitly
performs this coordinate permutation before comparing tables.

Exact checks:

* Existing multiplication/basis checks and symbolic norm composition.
* 64 left and 64 right polarized-alternative operator identities.
* Complete 512-by-64 Leibniz constraint matrix: rank 50, nullity 14.
* All 14 source-derived generators independent and in that kernel:
  **896 basis-product Leibniz tests**, plus unit/trace annihilation and
  norm skew-symmetry.
* Peirce evaluation rank 6; its kernel has dimension 8 and exactly the
  `M,-Mᵀ` blocks with `trace M=0`.
* Symbolic cross-product trace identity, with arbitrary matrix/vector entries.
* All 14 circular export matrices, all 14 aligned CAS matrices and all
  **196 operator brackets**; 120 stored nonzero structure constants.
* All **49** seven-generator Clifford operator anticommutators.
* Full local-triality constraint matrix: 512-by-192, rank 162, nullity 30;
  all **900** brackets of its rational basis triples remain in the kernel.
* Adding norm skew-symmetry gives rank 164 and nullity 28.
  The diagonal triality equations equal the derivation equations exactly.
* Existing off-diagonal owner: six independent generators, nine upper and
  nine lower brackets, skew-norm identity and symbolic quadratic expansion.
* Sage independently confirms ranks **50, 14, 6, 162, 164** for the derivation
  constraints, native basis, Peirce evaluation, triality constraints and
  skew-triality constraints, respectively.

Ranks/dimensions here are exact over QQ, not finite-field experiments or
claims about arbitrary characteristic. Expanded integer polynomial identities
are distinguished from these characteristic-zero rank calculations.

## Corrections to the proposed mathematical stream

### 1. Off-diagonal signs

For the repository's product (negative upper cross term, positive lower cross
term), the existing owner uses

```text
D(p,q)(a,u,v,b) =
  (p·v-q·u, (b-a)p+q×v, (a-b)q-p×u, q·u-p·v).
```

Its full-operator brackets are

```text
[D(p,0),D(r,0)] = D(0, 2(p×r))
[D(0,q),D(0,s)] = D(-2(q×s), 0).
```

The prompt instead reverses the two diagonal-to-vector differences but keeps
the other terms. This is not a derivation. Over QQ, take `p=e0`, `q=0`,
`X=E11`, `Y=V0`. For the prompt's operator:

```text
D(XY) = 0,       D(X)Y + XD(Y) = 2 E11.
```

The norm-polarization skew residual on the same pair is `-2`.
For `p1=e0`, `p2=e1`, `H=E11-E22`, its proposed commutator identity gives
`-4 V2 = 2 V2`, also false.

All three statements were checked in Lean, not just CAS:
`/tmp/gunaydin_gursey_prompt_counterchecks.lean`, exit 0;
`/tmp/gunaydin-gursey-prompt-counterchecks.log` lists only allowed axioms.
No proposed replacement carrier was installed.

### 2. Split versus division Clifford signature

For imaginary split octonions the existing Clifford quadratic form is
**minus the split norm**. On
`(E11-E22, U0+V0,U1+V1,U2+V2,U0-V0,U1-V1,U2-V2)` its signs are
`(+,+,+,+,-,-,-)`. Thus this real operator construction is `Cl(4,3)` under
the positive-first convention, not the division-octonion `Cl(0,7)` statement.
This is an associative operator representation, not an associative embedding
of the octonion multiplication.

### 3. Triality needs the correct carrier

The displayed Leibniz relation for **linear** triples alone has dimension 30
over QQ. Norm-skew triples have dimension 28. The two extra scalar directions
are visible directly: `((a+b)I,aI,bI)` satisfies the relation. Consequently the
unrestricted relation cannot by itself be identified with `so(4,4)`.

The prompt uses unbundled functions, omitting linearity; its `Iff.rfl`
identifies two identical predicates but does not construct a D4 triality
automorphism or prove its fixed algebra is a particular real form of G2.
The repository's generic triality and derivation owners do retain linearity.

## Verification history and limits

Initial combined build encountered an in-progress concurrent edit in
`OffDiagonalDerivation.offDiagonalDerivation_injective`. The other writer
corrected it; the final narrow build and 15-declaration audit pass.

Initially three CAS export/replay modules failed the axiom allowlist.
Concurrent edits changed `rootDerivationRationalTable_matrix`,
`casBasisMatrix_eq_aligned` and `casBracket_eq_structure_constants` to
`decide +kernel`. This audit did not make those edits. All changed owners
were rebuilt and independently re-audited. The final twelve-module replay
passes; earlier failure logs describe superseded snapshots, not remaining
failures. The final JSON was regenerated twice after the repairs.

Logs:

* `/tmp/gunaydin-gursey-core-owner-build.log`
* `/tmp/gunaydin-gursey-offdiagonal-build.log`
* `/tmp/gunaydin-gursey-cas-replay-recheck.log`
* `/tmp/gunaydin-gursey-owner-axioms.log` (initial 11-module audit)
* `/tmp/gunaydin-gursey-offdiagonal-axioms.log`
* `/tmp/gunaydin-gursey-cas-axioms-final.log` (intermediate export repair)
* `/tmp/gunaydin-gursey-all-selected-final-build.log` (**final build**)
* `/tmp/gunaydin-gursey-all-selected-final-axioms.log` (**final all-PASS audit**)
* `/tmp/gunaydin-gursey-cas-repro-{1,2}.json` (identical final CAS runs)

Deep-search packet: `/tmp/gunaydin-gursey-deep-search.{json,md}`. It includes
repo-owned lexical, entrypoint, graph/index-surface and filtered external-ref
lanes; actual source was inspected afterwards. The bounded external-ref
query returned no hits; that is not a claim that no relevant external work
exists. Existing generated CAS literals were checked, not accepted as proof.

The paper text and its numbered equations were not authenticated. Pauli/BdG
readout owners were located, but this audit does **not** certify the paper's
specific Appendix-D twisted 4-by-4 product isomorphism, nor claim it absent
repo-wide. No physics, global group classification or continuum claim follows
from this audit. No umbrella-wide axiom certification is asserted.

## Reproduction

The system `python3` lacks SymPy; the existing Sage environment was used,
without changing dependencies:

```sh
/home/goutev/miniforge3/envs/sage/bin/python \
  scratch/cas/gunaydin_gursey_existing_owners.py > /tmp/gg-owner-cas.json
cmp /tmp/gg-owner-cas.json docs/GUNAYDIN_GURSEY_EXISTING_OWNER_CAS.json
```

Run verification sequentially, after compiler-process inspection, under
`/tmp/info-geometry-build.lock` using `tools.build_lock.acquire_build_lock`.
For Lean, build selected modules with
`python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock ...`,
then run `lake env lean --run tools/infra/axiom_check.lean ...` on their oleans
while holding the same shared lock.

Receipt SHA-256:
`b339e2aa5557b162003cc2fe940baad764bb4e61321b0c6740a0166db20ba897`.

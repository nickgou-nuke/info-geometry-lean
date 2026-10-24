# Corrected Catto–Gürsey algebraic development

Historical verification: 2026-10-23 with pinned Lean v4.34.1.

## Current revision, 2026-10-24

Source review removed duplicate basis associator/Jacobiator proofs in favor of
`GunaydinGurseyTripleProducts.triple_associator` and `.triple_jacobiator`.
The duplicate color-square packet was removed; the existing
`PauliWeylTwistorQuarkColorBridge` owns both nilpotency lemmas.
The corrected aggregate imports the Hadronic owner. The separate Standalone
draft is excluded: its `uStar 0 = 0` contradicts its claimed mixed contraction.
A snapshot is preserved at
`scratch/rejected_CattoGurseyOctonionicStandalone_c9182c5800c72d85.lean.txt`;
another session recreated the live draft, which remains unaccepted.
The counts and hashes below describe the historical snapshot. Fresh QA of the
three corrected owners and aggregate is pending.


## Ground-truth contract and corrections

The multiplication owner is `InfoGeometry.Algebra.ZornVectorMatrix.mul`, with
minus lower-vector cross product in the upper slot and plus upper-vector cross
product in the lower slot. The previously supplied upper/lower basis assignment
contradicted that multiplication. We retain the existing, consistent
`Canonical.GunaydinGurseyQuarkBasisBridge` convention:

```text
uZero = E22, uStarZero = E11, u_i = V_i, uStar_i = -U_i.
```

Everything in the split-basis file is over an arbitrary `CommRing R`, except
that the no-faithful-associative-realization theorem explicitly adds
`Nontrivial R`. No inverse of two, finite-dimensional operator hypothesis,
positivity, or unproved inverse-existence assumption is inserted.

The new `splitCoordinates` is a native linear equivalence

```text
(R × R × (Fin 3 → R) × (Fin 3 → R)) ≃ₗ[R] ZornVectorMatrix R
(a,b,x,y) ↦ [[b,-y],[x,a]].
```

Its inverse and full multiplication transport are proved. `signedBasis` is a
native `Module.Basis` indexed by `Unit ⊕ Unit ⊕ Fin 3 ⊕ Fin 3`; the two singlets
and six signed colors are proved to be exactly its vectors. This proves an
actual eight-coordinate realization, not a proxy witness packet or a claim
that merely defining eight vectors proves an isomorphism.

## Lean owners and established scope

### `lean/InfoGeometry/Canonical/CattoGurseySplitBasis.lean`

- Native coordinate equivalence, full multiplication transport, and basis.
- Singlet resolution of the unit; existing singlet idempotency, orthogonality
  and triplet absorption lemmas are imported rather than redeclared.
- All anti-triplet absorption laws.
- Complete fusion laws indexed by `Fin 3 × Fin 3`, with coefficients given by
  the existing cross product: reverse orientations and repeated indices included.
- Both mixed contraction endpoints and all CAR-type anticommutators.
- Characteristic-independent square-zero of all six color generators.
- Generic determinant-valued triple products, with both parenthesizations.
- Basis associator `uZero - uStarZero`, nested commutator coefficient `-2`,
  cyclic Jacobiator coefficient `-6`, grading square and anticommutation.
- Exact criterion: the cyclic Jacobiator is nonzero iff `(6 : R) ≠ 0`.
- No injective additive multiplication-preserving map into any associative
  ring when `R` is nontrivial. Thus the proposed arrow to ordinary matrix
  multiplication cannot be interpreted as a faithful algebra realization.

### `lean/InfoGeometry/Canonical/CattoGurseyBlockGrading.lean`

- Native `SuperMatrix m n R`, not a generic ring relabeled as dimension 27.
- Two complementary block supports and their four exact compressions.
- Equality between the existing block split and native Peirce linear maps.
- Equivalence of `IsHomogeneous` predicates with membership in the Peirce
  projection ranges; hence the actual internal direct sum from `PeirceGrading`.
- Square-zero of each directed odd block; no such assertion for their sum.
- `supertrace (1 : SuperMatrix 6 21 R) = -15`.

The existing `GLSupermatrixGradedLie` owner supplies the actual homogeneous
superbracket, parity closure, graded skew symmetry, super-Jacobi,
super-adjoint derivation, and supertrace laws. These were included in the
all-declaration axiom audit, rather than duplicated as specialized wrappers.

### `lean/InfoGeometry/Superalgebra/CattoGurseyOctonionicHadronicSuperalgebra.lean`

The broken pasted module was replaced by imports of those owners and a
substantive `composite_sector_resolution` for actual `SuperMatrix 6 21 R`.
Every block of `Psi * Phi` retains **both** contributions, e.g.
`A(Psi*Phi) = A(Psi)*A(Phi) + B(Psi)*C(Phi)`.
The arbitrary second input is not assumed to be an adjoint.

Kernel-checked regression theorems also establish:

- characteristic three: zero Jacobiator but nonzero associator;
- integers: genuinely nonzero Jacobiator;
- a transpose-paired swap-matrix counterexample to the assertion that
  `Psi * P * PsiBar` must lie in the original `P A P` corner.

The existing import in `lean/InfoGeometry/All.lean` points to this entrypoint.
The prior duplicate-carrier file was unchanged for several minutes before
replacement, with no active compiler on it. Its complete snapshot is preserved
at `/tmp/catto-gursey-before-native-replacement.lean` (SHA-256
`7b0cd8a6ebe0014e3f29690e36698b37b3718222898ecdc73d276c19d6586df0`).
No consumers of its old declaration names were found in the searched `lean`,
`proofs`, and `tests` sources outside that file.

## Verification

Locked explicit/aggregate entrypoint build succeeded (8935 jobs):

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Superalgebra.CattoGurseyOctonionicHadronicSuperalgebra
```

Final build log: `/tmp/catto-native-root4.log`.
All three changed Lean files are warning-free. Existing style warnings in
`GLSupermatrixGradedLie` and dependency-local-change notices remain unchanged.
A full-superproject default-target build was **not** performed.

`tools/infra/axiom_check.lean`, under the shared build lock, replayed and audited
**every declaration** in these seven selected owners, including transitive
axioms:

| Module under `InfoGeometry` | Audited declarations |
| --- | ---: |
| `Algebra.ZornVectorMatrix` | 524 |
| `Canonical.GunaydinGurseyQuarkBasisBridge` | 15 |
| `Canonical.CattoGurseySplitBasis` | 33 |
| `Canonical.GLSupermatrixGradedLie` | 103 |
| `Canonical.CattoGurseyBlockGrading` | 12 |
| `Core.PeirceGrading` | 59 |
| `Superalgebra.CattoGurseyOctonionicHadronicSuperalgebra` | 4 |
| **Total** | **750** |

All passed. Log: `/tmp/catto-native-axioms.log`. The only allowed axioms were
`propext`, `Classical.choice`, and `Quot.sound`.

Source-aware scans of the three changed Lean files mask comments, strings and
quoted identifiers and reject active `sorry`, `admit`, `sorryAx`, `axiom`,
`postulate`, `unsafe`, `partial`, and `#exit`: PASS. Staged whitespace checks:
PASS. No commit was created; changes are staged.

The deterministic standard-library script
`scripts/check_catto_gursey_conventions.py` checks all 64 integer structure
constants of the signed coordinate transport, CAR, and associator/Jacobiator
signs. It records the exact basis and coordinate order, with no anti-homomorphism.
Its checks are supplementary; the general-ring proofs are Lean proofs. The
Lean `fusion_table` and `splitCoordinates_mul` also establish the basis-aligned
round trip, not merely the script's finite arithmetic assertions.

## Explicit interpretation boundary

This is the corrected algebraic development, not a verification of the original
PDF transcription or hadronic representation-theory claims. CAR-type scalar
anticommutators do not identify the nonassociative product with the universal
associative CAR algebra. No central-extension structure, `SU(6|21)` real form,
complex-octonion `i e7` identification, or physical confinement theorem is
asserted. Those are distinct mathematical constructions, not consequences
hidden inside the multiplication table. The associative and nonassociative
carriers remain separate, with a proved obstruction to the alleged faithful
multiplicative identification.

## Source hashes

```text
4ba776e05f16e032cd33827c2c5181074af40fa719f5c67fdbc3e2fd46c3be8b  lean/InfoGeometry/Canonical/CattoGurseySplitBasis.lean
a0440bb452f371eb84210c3507e310f5f826c313461608e551754fbeb67c9aeb  lean/InfoGeometry/Canonical/CattoGurseyBlockGrading.lean
61ca22b7005ce2369b1ee2cb5790d62a4cdcbd49e28b977d28710cb95b62219a  lean/InfoGeometry/Superalgebra/CattoGurseyOctonionicHadronicSuperalgebra.lean
```

## Final independent replay, 2026-10-24

The three corrected octonion owners now have 30 + 12 + 4 = 46 axiom-clean declarations after duplicate removal.
The five rechecked owners passed with 81 declarations total. Exact Core.All and
InfoGeometry.All builds passed (9011 and 26980 jobs respectively), with stable
seven-source/pin hashes and no scoped warnings. Existing imported warnings remain.
Receipt: `/tmp/qa-a-catto-retry2-j1uswpr6/result.json`. Aggregate compilation is not an all-imported-declaration
axiom audit or clean-release certification.

Current selected source hashes:

```text
dbaedda7dd9de84e39a68b9fde31379881b74c80f643b9353d381dc505cf72b3  lean/InfoGeometry/Canonical/CattoGurseySplitBasis.lean
f96eaddc904397bd2caf18e06490d2547675898abeb818cd9b8d85b95367ddad  lean/InfoGeometry/Canonical/CattoGurseyBlockGrading.lean
6ca073eca2f944438c242a075f59899b33b59b85a9b83dd7377d98cdbba7bd3f  lean/InfoGeometry/Superalgebra/CattoGurseyOctonionicHadronicSuperalgebra.lean
2d6caf71e4674dc8788b7adffdadf91040790f8d310597480ba2bc5f761e7133  lean/InfoGeometry/Core/BosonFermionRegression.lean
cc902922dd30965ef0ddfa2ed68f501ecdefa1ab6bbc03faeed89c81604ce8c9  lean/InfoGeometry/Core/NilpotentCartanRegression.lean
7f6fcf1befcfab57bb3a4ffe11f0855fb4248302e178171e4c2c8044406f16ac  lean/InfoGeometry/Core/All.lean
fbe04fa6993ead97420c2393e0fe11716accfe5f3a34dad5691a0762c2e11fa1  lean/InfoGeometry/All.lean
```

## Original-paper reference supplied on 2026-10-24

DOI `10.1063/1.1666240` identifies Murat Günaydin and Feza Gürsey,
*Quark structure and octonions*, Journal of Mathematical Physics 14(11),
1651–1667 (1973). Publisher metadata and abstract were checked at
https://pubs.aip.org/aip/jmp/article-abstract/14/11/1651/440804/Quark-structure-and-octonions .
The publisher PDF was not retrievable in this session; the local browser
connection was unavailable. No equation-level transcription verification is
claimed from that abstract. `GunaydinGurseyQuarkBasisBridge.lean` already cites
this original paper and records the repository's signed Zorn convention.
The kernel results above certify the precise Lean statements independently of
whether the paper uses the same coordinate convention.

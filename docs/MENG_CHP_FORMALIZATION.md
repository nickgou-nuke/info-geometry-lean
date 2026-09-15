# Meng ChP: source-to-Lean translation

## Downloaded primary sources

- [Jie Meng, TD Lee presentation](https://indico-tdli.sjtu.edu.cn/event/2611/contributions/13656/attachments/5247/8678/Meng20241206%40ChP-violationTDLee.pdf), 46 pages; local copy: `papers/meng_nuclear_chirality/chp-violation-td-lee.pdf`.
  SHA-256: `a38b18d69bb32aff3a82c9510c809cbb874e3d9235580a0ab486993dc5f81113`.
- [Wang, Wu, Zhang, Zhao and Meng, Science Bulletin 65 (2020), 2001](https://arxiv.org/abs/2006.12062); local copy: `papers/meng_nuclear_chirality/chp-selection-rules.pdf`.
  SHA-256: `b497212dbece2dfa15671390468488bb64b06768e56e47241181ee4f26b86f01`.

Presentation pages 40 and 42 were rendered and visually checked because PDF text extraction omits the displayed operator equations. The embedded PDF title is stale; it is not used as bibliographic evidence.

## What the source says

Slide 40 defines chiture `A = R₃(π/2) C π` and chiplex `B = PA`; the paper writes `B = AP`. Here `C` exchanges particle and hole, not particle and antiparticle. The paper (pages 3–6) imposes an ideal reflection-asymmetric triaxial particle-rotor model, matched particle/hole shells and neglected spherical single-particle splitting for the extra symmetry. Even core projections give chiture/chiplex labels ±1. Intrinsic nuclear symmetry breaking is not a demonstrated violation of fundamental CP or CPT.

Slide 42 gives the following necessary transition conditions:

| Multipole | Chiture | Total parity | Cπ | Chiplex |
|---|---|---|---|---|
| E2 | changes | preserved | preserved | changes |
| M1 | changes | preserved | changes | changes |
| E3 | preserved | changes | preserved | changes |

These conditions depend on the ideal model's electromagnetic operators; permitted transitions need not have nonzero amplitudes.

## Formal owner files and exact scope

### Selection-rule algebra

`lean/InfoGeometry/Physics/MengChPSelectionRules.lean` uses native complex linear maps and the algebraic dual. It proves:

- multiplication of parity and chiture eigenvalues for `B = AP`;
- covariance characters multiply under composition of symmetry operators;
- a transition amplitude vanishes when its initial/final characters mismatch;
- same-chiplex amplitudes vanish for the E2/M1/E3 character table, **assuming** the corresponding operator covariance and eigenstate hypotheses.

The general selection lemma also applies to the Cπ column. No electromagnetic covariance is manufactured from an operator name. Identifying a dual functional with a physical bra requires the usual Hilbert-space interpretation, which is not assumed implicitly.

### Five grades and circular phases

`lean/InfoGeometry/Physics/NuclearFiveGradeCircularPhase.lean` extends the existing two-mode CAR endomorphism owner. For its centered number operator `H`, it constructs

`U = 1 - H² + iH = diag(-i, 1, 1, i)`.

It proves `U⁴ = 1` and `U X = i^degree(X) X U` for all seven named generators occupying grades -2 through 2. Both pair channels acquire -1, individual creation/annihilation channels acquire ±i, and the Cartan channel is unchanged. This is a proved discrete realization of the existing adjoint grading, not an identification with the generic Freudenthal five-grading or the physical core angular momentum.

The existing finite Soloviev operator obeys `U H(V) = H(-V) U`. Consequently, a bare quarter-turn is not in general a Hamiltonian symmetry; further exchange/reflection factors are necessary. The source's chiture operator and this CAR quarter-turn are not equated.

### Operator-Zorn circular phase convention

`lean/InfoGeometry/Physics/MengCircularOperatorZorn.lean` uses the existing **associative** `OperatorZornMatrix` owner, not split-octonion multiplication. For operator coefficients and any operator `J` satisfying `J² = -1`, conjugation by `diag(J,1)` is multiplicative. No commutativity of the operator coefficients is assumed. The upper/lower rails transform as `J V` and `W(-J)`; the first diagonal entry also transforms by conjugation.

For scalar `J=i`, this rephases the existing two chiral sectors of the finite Soloviev matrix: its off-diagonal couplings become `iV` and `-iV`. The characteristic determinant remains `(Eqp-E)(Eqp+ω-E)-V²`. This is a phase convention within a chiral basis, not a newly constructed basis for the full nuclear rotor Hilbert space.

## Dependency branches and remaining work

The subsequent [whole-repository Soloviev/Kantor audit](MENG_SOLOVIEV_DEEP_REUSE_AUDIT.md)
supersedes any reading of this section as an inventory of the entire codebase.
Existing owners already connect five-grade CAR, Zorn-valued phonon carriers,
projected Soloviev Hamiltonians, and operator-valued circular frames. The
three modules described above are not replacements for those owners.

```text
source operator definitions → covariance + eigenstates → selection rules
two-mode CAR → five-grade generators → circular phase covariance
                                    → Soloviev coupling sign reversal
associative operator-Zorn → invertible phase change → multiplicativity
finite Soloviev matrix + scalar phase change → unchanged secular polynomial
```

The arrows describe these proofs, not the complete repository import graph. The older `NuclearChiralMengBridge` collects abstract identities; its `chirality` field is not a formalization of antiunitary nuclear time reversal, and its rank order is not a source-derived physical dependency graph.

Not established by these new bridges: an intertwiner from the source RAT-PRM to the existing CAR/Soloviev carriers; the source electromagnetic covariance from spherical tensors; the source collective angular-momentum and octupole dynamics; quartet near-degeneracy; numerical transition strengths; an identification with thermal doubling, Aharonov two-state vectors, or Tomita conjugation. This is a boundary of this translation, not a claim that the repository lacks the underlying algebra or projection machinery. The downloaded presentation does not establish all these proposed identifications.

## Verification environment

The repository pins Lean 4.28.1, which is absent locally. Narrow checks use installed Lean 4.28.0, cached Mathlib, and isolated output under `/tmp/isnp-metacompiler-validation`, serialized by `/tmp/info-geometry-build.lock`. Dependency manifests and caches are not modified. This is not a claim of a successful full pinned-repository build.

All three new owner modules compile without warnings: 15 theorems in total.
`lean/InfoGeometry/Physics/MengChPTranslationTests.lean` also compiles without warnings (nine theorems/examples), including a forbidden transition, a nonzero opposite-sign transition, and operator-Zorn multiplication with noncommutative matrix coefficients. Fourteen principal theorems were audited with `#print axioms`; their dependencies are only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, custom axiom, or `native_decide` is introduced. Staged changes pass `git diff --check`.

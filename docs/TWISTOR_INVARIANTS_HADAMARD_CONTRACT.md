# Twistor invariants and native Hadamard transport

## Intake and scope

The source is the user's Bulgarian note supplied on 2026-11-11, headed
“Квантово-геометричен синопсис на разкритието”. It proposes an identification
of constituent rest mass with mutual Witt pairing, a Jordan/homotope
decomposition, and a Hadamard operator. Its final alternatives name a bound
`metricCount k ≤ 4^k` and an unspecified operator `L_J + θΩ`.

This is a theorem-bearing intake with physical interpretation outside the
finite algebraic acceptance target. The reviewed base is
`c143c264bc18bbf41d692be4e270b5b7f7405702`. Lean and Mathlib pins are preserved.
No claim about hidden reasoning or universal physical mass generation is made.

## Claim ledger

| Source claim | Exact mathematical disposition |
| --- | --- |
| `m² = 2 det P` for the stated momentum convention | A convention requiring the factor two throughout. The existing owner proves `2 * det P = 2 * pairMassSq`. |
| `det(P(Z)+P(W)) = |I(Z,W)|²` | Existing theorem plus the definition of the lower-spinor minor; reuse it without a duplicate wrapper theorem. |
| `m² = |wittPair Z W|²` universally | Countermodel: `Z=(0,e₀)`, `W=(0,e₁)` are nonzero Witt-null, mutually orthogonal, and have momentum determinant one. |
| Nonzero mutual Witt pairing forces positive mass | Countermodel: `Z=(0,e₀)`, `W=(i e₀,e₀)` are nonzero Witt-null, have pairing `i`, and have momentum determinant zero. Both lower spinors are nonzero. |
| Hermitian Gram determinant on two null twistors | It is **minus** the squared norm of the mutual Witt pairing. It is a different determinant from the momentum determinant. |
| Infinity twistor is a Peirce projector | The covariant infinity twistor is a map to the dual, not an endomorphism. The existing sharp-plus-Witt-dual endomorphism is antilinear, nonzero, and square-zero. |
| Symmetrized homotope preserves associativity | The ordered product `x * T * y` is associative. Its symmetrization is generally not associative. Ordered multiplication is recovered from symmetric and antisymmetric parts with the factor two explicit. |
| Hadamard change of basis generates mass | Only finite matrix identities and an invertible change of coordinates are in scope. No physical mass-generation theorem follows from a coordinate change. |
| `metricCount k ≤ 4^k` needs an `omega` repair | No declaration or reported diagnostic was located in the inspected canonical/mirror Lean sources and related docs. A conditional induction requires a separately proved base case and recurrence. |
| `L_J + θΩ` lifts to a Maurer–Cartan kernel | No definition of `θΩ` or the asserted lift was supplied or located. Do not identify it with another operator by analogy. |

## Actual carriers and owners

`PenroseIncidence.Twistor4` is `(Fin 2 → ℂ) × (Fin 2 → ℂ)`.
`PerjesConventions.wittPair` is conjugate-linear in the first argument.
`TwistorKinematicTensor.momentum Z` is
`Matrix.vecMulVec (star Z.2) Z.2`.
`InfinityTwistor.infinityTwistor Z W` is the alternating lower-spinor minor.
The separate symmetric kinematic tensor is not the alternating Plücker bivector.

Reuse these declarations and their exact hypotheses:

- `TwistorConstituentKinematics.pairMomentum_determinant`,
  `paper_pair_mass`, `massive_pair_witness`, and the existing zero/positivity
  characterizations.
- `PerjesConventions.wittPair_conj`, `wittToDiagonal`, `diagonal_pairing`,
  and `paperIncidence_witt_isotropic`.
- `TwistorKinematicTensor.infinityConjugate_sq` and the explicitly defined
  `infinityConjugate`.
- `NonCommutativeTwoStateAndModularShift.Mat2`, `H_Walsh`, and the existing
  Walsh/Hadamard identity in `PeirceSpine/TwoStateModularShiftGeometry.lean`.
- `FiniteMatrixNoncommutativeWitness.matrix_units_noncommute_of_nontrivial`,
  a direct imported witness on native two-by-two matrices over every
  nontrivial ring; no duplicate witness is introduced.
- `LieJordanEndomorphisms`' native `Module.End` operators. Their carrier
  retains multiplication order in an arbitrary associative ring.

The smallest missing implications are the separation of the two twistor
invariants on actual null vectors, the Hermitian Gram sign identity, and a
faithful transport from the existing four-entry matrix carrier to Mathlib's
`Matrix (Fin 2) (Fin 2) B`.

## Dependency order

1. Existing spinor and twistor definitions determine the two pairings.
2. The lower-spinor dyads and their determinant determine `pairMassSq`.
3. Hermitian symmetry determines the Gram determinant independently.
4. Explicit null pairs disprove either proposed implication between the
   vanishing of these invariants.
5. A ring equivalence transports the existing ordered matrix operations to
   native `Matrix`; a Hadamard calculation then holds for arbitrary entries.
6. Invertibility of `2` is an explicit additional hypothesis whenever the
   unnormalized Hadamard matrix is used as an invertible similarity.

These are mathematical dependencies, not a claimed causal derivation of
particle physics. No completion, colimit, dynamics, units convention, or
Pauli–Lubanski reconstruction is supplied by the finite identities alone.

## Source and literature review

Canonical and mirror owner searches distinguished the infinity pairing from
the Hermitian pairing, and the existing custom `Mat2` from unrelated matrix
carriers with similar names. A bounded search for `metricCount`,
`metric_count`, and the named superoperator did not locate their definitions.
Nearby `fourword_count` and `matStage_finrank` count different objects.

Primary references distinguish the alternating scalar `f` from Hermitian
cross-pairing `ρ` and helicity differences; their normalization must be
matched before using their physical mass or spin formulas:

- Andreas Bette and Stanisław Zakrzewski,
  [Massive Relativistic Systems with Spin and the Two Twistor Phase Space](https://arxiv.org/abs/hep-th/0404024),
  equations (1.7), (1.12)–(1.16), (1.21)–(1.28).
- Andreas Bette, José A. de Azcárraga, Jerzy Lukierski, and C. Miquel-Espanya,
  [Massive Relativistic Particle Model with Spin and Electric Charge from Two-Twistor Dynamics](https://arxiv.org/abs/hep-th/0405166),
  equations (1.2), (1.9), (1.11a)–(1.11b), and (2.17).

## Acceptance record — 2026-11-11

**Status: kernel_verified for the finite algebraic statements below.** The
physical interpretations remain limited by the claim ledger. The count
example is conditional on its stated recurrence; `metricCount` and `θΩ`
remain unidentified source objects.

The focused command, run through the shared build lock, was:

```bash
python3 verification/twistor-hadamard/check.py build
```

It exited **0**, reporting `Build completed successfully (3282 jobs)`.
The package covers 36 repository modules in the reconstructed source closure,
including the four changed mathematical owners and the Audit. Mathlib and
other dependency artifacts were reused at their pinned revisions; this is not
a fresh rebuild of all Mathlib source or the entire parent repository.

The output explicitly records a **fresh build** of
`InfoGeometry.Canonical.TwistorHadamardAudit`, not a replay of an old audit.
That elaboration checks both examples: the exact mass/infinity identity and
the induction from the explicit count assumptions. It prints all **14 new
public declarations** (three definitions and eleven theorems), plus the
reused generic noncommutativity theorem. Independent comparison of source and
output found **15 reports, no missing or duplicate reports, and no disallowed
axioms**. The exact union is:

```text
propext
Classical.choice
Quot.sound
```

The environment is Lean **4.34.1**, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`, and Lake
`5.0.0-src+5045d00`. All nine dependency checkouts match the focused manifest
and have clean tracked sources. The parent toolchain and dependency manifest
are unchanged.

The staged proof gate passed with exit **0** after reusing the existing
generic matrix-unit witness. Placeholder scans of all five touched Lean
files found no proof holes, custom axioms, or unsafe bypasses. The regex
vacuity linter's findings concern pre-existing inverse-law simplifications,
next-line term proofs, and parameters used through the goal; an independent
source review classified these as false positives without suppressions.

Independent semantic review covered the exact hypotheses, arbitrary-entry
matrix formula, inverse normalization, both actual null-twistor witnesses,
and the Gram determinant sign. The following hashes were unchanged between
that final review and successful compilation:

| Lean file | SHA-256 |
| --- | --- |
| `Twistor/PerjesConventions.lean` | `903b0b7a18386048fa13266ff8adcbadd8c14bb0e6a9c32ab5da6a3049a2ee9d` |
| `Twistor/TwistorKinematicTensor.lean` | `f89010846129b1f1ce1db809873ef1548efbe321c9beb53502000fe7eafcb0bc` |
| `Twistor/TwistorConstituentKinematics.lean` | `2347b498be655c0fa6e6ddeac319519830bca9a13dcb290ef937d8d0ad91203f` |
| `OperatorAlgebra/PeirceHadamardNative.lean` | `79b97988a464868ffa9bc739502b59ef1c9ae13b19b6296798739e64b4f10819` |
| `Canonical/TwistorHadamardAudit.lean` | `55cfdae63d52ea11401d019699d9cc7efc33df4e61e07016d21f5a603e3e4bae` |

The successful build log has SHA-256
`3b19eff5727f1f9fa69014e85387db9e3f92568919bf00456b2930a33f0c3d15`.
Its warnings concern existing declarations and deprecated dependency imports;
none is attached to a new declaration. Initial elaboration errors in the
Gram and arbitrary-matrix proofs were corrected by normalizing
`starRingEnd_apply` and unfolding native `Matrix.vecMul`/`dotProduct`, without
changing statements or hypotheses.

## Root-package and publication boundary

The separate prerequisite check

```bash
python3 tools/infra/ci_bootstrap.py paths --root .
```

exited **1**. The root package lacks the configurations for
`HomotopyHypothesis` and `Atlas` (untracked path dependencies), and `GIFT` is an
uninitialized gitlink at its recorded commit. `InfoGeometryCore` is present.
No dependency was replaced with a stub or an arbitrary upstream revision.

The focused result does not certify the root package or waive its publication
gate. Existing caches, dependency pins, and other sessions' work were
preserved. The required pre-push gate remains unpassed.

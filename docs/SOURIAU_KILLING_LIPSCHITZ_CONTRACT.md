# Souriau Killing Lipschitz bridge: theorem contract

> **Module disambiguation note (PR #426 adaptation):** On `main`,
> `lean/InfoGeometry/Canonical/SouriauKillingLipschitzBridge.lean` owns the
> finite `Cl(1,1)` Minkowski/Rindler boost and Kosmann-bivector bridge.
> Accordingly, PR #426's doubled-real-Krein bridge and its generated axiom
> audit are integrated on `main` as
> `lean/InfoGeometry/Canonical/SouriauDoubledKreinLipschitzBridge.lean` and
> `lean/InfoGeometry/Canonical/SouriauDoubledKreinLipschitzBridgeAudit.lean`.

## Intake and source revision

The intake on 2026-11-21 was the identifier `SouriauKillingLipschitzBridge`.
No theorem statement accompanied it. The implementation below selects the
analytic commutator-seminorm connection supported by the current owners; it
does not claim to recover an earlier unstated specification.

Base revision: `586c14bc9fb94eb09b56f7dc850d9d5297269f91` of
`nickgou-nuke/info-geometry-lean`. Lean and Mathlib pins remain unchanged.

### Doubled real Krein refinement

The follow-up intake on 2026-11-21 is: “move to double real krein spaces”.
The starting verified checkpoint is
`f467062ea84afb45b089c5cd676af5ca45a9bbdb`.

The existing carrier is already `DoubledSpace E = WithLp 2 (E × E)`.
For complete real `E`, use its canonical `instKreinSpaceProdL2` instance,
whose fundamental symmetry is `spectral_epsilon`, with signed pairing
`[(x, ξ), (y, η)] = inner ℝ x y - inner ℝ ξ η` and Krein adjoint
`A♯ = spectral_epsilon.comp (adjoint A).comp spectral_epsilon`.
The modular swap `modular_j` is a different real operator.

The verified refinement connects the existing commutator bridge to that
actual Krein structure:

1. `G(h)♯ = clockAxis.comp (h♯)`; a Krein-self-adjoint seed that anticommutes
   with `clockAxis` gives a Krein-skew generator.
2. A Krein-skew generator makes the existing exponential flow a
   `KreinSpace.IsKreinIsometry`, by the existing
   `InfoGeometry.Krein.exp_preservesMetric` theorem from
   `Krein/ExponentialIsometry.lean`.
3. The seed `h = -spectral_epsilon` gives `G = modular_j`, yielding a
   concrete doubled real boost family on arbitrary complete real `E`.
   Its action on the grading is `δ(-spectral_epsilon, spectral_epsilon) =
   2 • clockAxis`. Both the generator and this action are proved nonzero
   under `[Nontrivial E]`.
4. For a Krein-skew generator, the derivation intertwines the Krein adjoint
   and preserves both Krein-self-adjoint and Krein-skew-adjoint sectors.
5. The actual signed readout `A ↦ [δ(A) u, v]` has native Lipschitz bound
   `‖u‖₊ * ‖v‖₊ * (2 * ‖G‖₊)` in the associated Hilbert operator norm.

The general finite-time state-flow bound uses its actual operator norm.
The existing Hilbert `Isometry` theorem retains its separate
hypotheses. The indefinite quadratic form is never used as a metric norm.
No replacement carrier, complex scalar, or preservation certificate field
is introduced. The refinement adds 17 theorems; its build, warning check,
and the expanded 56-declaration axiom audit passed.

## Source-grounded scope

Let `E` be a complete real inner-product space, let
`H₂ := InfoGeometry.Krein.DoubledSpace E`, and let `EndH := H₂ →L[ℝ] H₂`.
For a fixed operator seed `hMod : EndH`, the existing
`BogoliubovTransport` owner defines

```text
G := relativeModularKGenerator hMod = hMod.comp clockAxis
δ(A) := relativeModularDeriv hMod A = G.comp A - A.comp G.
```

The phase axis is the existing real doubled-space operator. No complex scalar,
finite matrix replacement, trace, or external manifold is introduced.
The native Krein class and analytic flow results use completeness. The
algebraic commutator, ordinary norm bounds, and spectral-distance statements
also hold on an arbitrary real inner-product space.

The higher `ThermodynamicGenerator` owner defines its Souriau temperature
vector by the same generator construction at `P.modularData.modularSeed ψ`.
Its `IsPotentialKillingOperator P ψ A` predicate is exactly the vanishing of
the resulting induced derivation. This bridge works at the shared
`BogoliubovTransport` owner, on the actual bounded noncommutative operator
algebra, without importing unrelated higher thermodynamic dependencies.

## Verified statements

1. The existing Connes commutator interface, instantiated with `dirac := G`,
   has commutator exactly `δ(A)`.
2. Its commutator norm is zero exactly when `δ(A) = 0`, equivalently
   `Commute G A`. This uses a norm, not a scalar probe-faithfulness premise.
   The condition is also equivalent to exact exponential conjugation fixing
   `A` at every real time; the reverse implication uses the actual derivative
   of the transport at zero.
3. Its Lip-1 condition is exactly `‖δ(A)‖ ≤ 1`.
4. For an arbitrary normed noncommutative ring and fixed `D`,
   `‖[D,A]‖ ≤ 2 * ‖D‖ * ‖A‖`, and both `A ↦ [D,A]` and
   `A ↦ ‖[D,A]‖` are native `LipschitzWith (2 * ‖D‖₊)` maps.
5. Over a real normed algebra, the commutator norm is a native
   `Seminorm ℝ A` and satisfies the Leibniz estimate. The seminorm may
   have a nontrivial kernel.
6. If two additive real readouts differ on an observable with `δ(A) = 0`,
   the existing spectral-distance value set is not bounded above.
7. Under the existing self-adjointness and phase-linearity hypotheses on
   `hMod`, the actual exponential transport is a positive-Hilbert isometry,
   and therefore `1`-Lipschitz. Krein-skewness alone is not used to infer this.

The Lipschitz estimates vary the observable at a fixed generator. They do
not assert regularity of an arbitrary state-dependent seed as the state varies.

## Owners and reuse

| Owner | Reused mathematical content |
| --- | --- |
| `Canonical/BogoliubovTransport` | Real doubled-space generator, commutator derivation, exact exponential transport, positive-inner-product preservation under stated seed hypotheses. |
| `Canonical/ConnesSpectralTripleBridge` | Bounded algebra-element commutator interface; extended here with generic norm estimates and native seminorm construction. |
| `Canonical/ConnesNCSpectralMetricSupremum` | Spectral-distance value set and its unboundedness when additive readouts distinguish a commuting observable. |
| `Krein/KreinSpace` and `Krein/DoubledSpace` | Canonical diagonal Krein instance, fundamental symmetry, signed pairing, Krein adjoint, real Clifford-axis identities, and pairing bound. |
| `Krein/ExponentialIsometry` | Krein-skew generators exponentiate to actual Krein-isometric flows. |
| `OperatorAlgebra/KreinInnerDerivation` | The commutator with a Krein-skew generator intertwines the Krein adjoint; the bridge reuses this theorem. |
| Mathlib normed-ring, seminorm, and Lipschitz APIs | Submultiplicative norm, norm-difference bound, native `Seminorm` and `LipschitzWith`. |

`SouriauKillingFlow` was inspected separately. Its current theorem is a
phase-correlation sign-reversal theorem under modular `J` reflection; that
theorem is not a Killing-flow or Lipschitz estimate.

## Boundaries

- The repository's `ConnesSpectral.SpectralTriple` stores a bounded algebra
  element. Instantiating it does not construct an unbounded self-adjoint Dirac
  operator, compact resolvent, or a full analytic spectral triple.
- The norm is the positive Hilbert operator norm. The indefinite Krein form
  is not treated as a metric norm.
- The kernel condition concerns stationary observables for a fixed inner
  derivation. It is not a manifold Killing-field construction or a statement
  about the Lie-algebra Killing form or Clifford Lipschitz group.
- The existing real-valued supremum is not reported as `+∞` when its defining
  set is unbounded. The theorem states `¬ BddAbove` exactly.
- A scalar first-variation reading need not detect the whole commutator.
  No `ProbeFaithful` assumption is introduced.

## Verification results and scope

The focused package under `verification/souriau-killing-lipschitz` builds the
actual parent-repository source files using the unchanged Lean and Mathlib
pins. Its wrapper acquires the repository's shared build lock. The audit
prints the axiom dependencies of every explicit public declaration in the
changed mathematical owners and rejects dependencies outside `propext`,
`Classical.choice`, and `Quot.sound`.

Compilation, axiom audit, source screening, and semantic review are separate
checks. The final build, warning checks, and Lean axiom audit ran sequentially
within one shared-lock transaction. No whole-repository build is claimed by
this focused verification.

| Check | Recorded result |
| --- | --- |
| Independent semantic review | Accepted the doubled-Krein signs, exact seed condition, native owner reuse, separate Hilbert/Krein isometry regimes, and nontriviality hypotheses; source hashes and validation records match. |
| Strict staged proof gate | Passed for the two mathematical owners and the audit module. |
| Explicit declaration inventory | 56 declarations in two mathematical owners; forbidden proof constructs absent. |
| Transitive source review | All 47 repository modules in the import closure present; comment/string-aware source scan found no proof holes, custom axioms, `native_decide`, or `unsafe`. |
| Toolchain identity | Lean 4.34.1, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`; pinned Mathlib checkout clean. |
| Focused Lean build | Passed for the bridge and generated audit module; Lake reported 3,571 jobs, including cached dependencies. |
| Warnings treated as errors | The refined `SouriauKillingLipschitzBridge.lean` passed `lean -DwarningAsError=true`. The unchanged Connes owner retains its verified source fingerprint from the starting checkpoint. |
| Transitive Lean axiom audit | All 56 inventoried declarations passed. The union of reported axioms is exactly `propext`, `Classical.choice`, and `Quot.sound`. |

The focused build replayed pre-existing warnings in unchanged imports. The
refined mathematical owner passed its separate warning-as-error check.
The reproducible commands are in the focused package's README.

### Verified source fingerprints

| Source | SHA-256 |
| --- | --- |
| `ConnesSpectralTripleBridge.lean` | `cce2e8d37feaba610437407fb3f1d2d67be1354c584ae2a402bc43b12d3d3512` |
| `SouriauKillingLipschitzBridge.lean` | `e715f7ad26cdbbe5b525ff3d4538968002078a119e095ad836472fbcd93f7175` |
| `SouriauKillingLipschitzBridgeAudit.lean` | `ffa976663dc2fb0cc1295f5b46bdbee5391ee489ead1a6577fae758b5feed277` |

The strict text screen initially flagged the pre-existing data-only
`SpectralTriple` structure because no inhabitant was recognizable in that
same file. A native `Inhabited` instance using the zero Dirac element resolves
that source-screen finding. It asserts inhabitation only, not nondegeneracy or
finite spectral distance. All estimates remain quantified over arbitrary
Dirac elements, and the Souriau adapter uses the actual modular generator.

The declaration-DAG status command could not load `dag-toolchain.json` in
the observed checkout. No live graph freshness or complete graph coverage is
claimed; source definitions, imports, and consumers were inspected directly.

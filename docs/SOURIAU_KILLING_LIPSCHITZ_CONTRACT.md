# Souriau Killing Lipschitz bridge: theorem contract

## Intake and source revision

The intake on 2026-11-21 was the identifier `SouriauKillingLipschitzBridge`.
No theorem statement accompanied it. The implementation below selects the
analytic commutator-seminorm connection supported by the current owners; it
does not claim to recover an earlier unstated specification.

Base revision: `586c14bc9fb94eb09b56f7dc850d9d5297269f91` of
`nickgou-nuke/info-geometry-lean`. Lean and Mathlib pins remain unchanged.

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
Completeness is used for the exponential-flow results; the algebraic, norm,
and spectral-distance statements also hold on an arbitrary real inner-product
space.

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
| Independent semantic review | Accepted mathematical design in the stated bounded-operator scope; the distinction between state-vector isometry and observable fixedness is preserved. |
| Strict staged proof gate | Passed for the two mathematical owners and the audit module. |
| Explicit declaration inventory | 39 declarations in two mathematical owners; forbidden proof constructs absent. |
| Transitive source review | All 43 repository modules in the import closure present; comment/string-aware source scan found no proof holes, custom axioms, `native_decide`, or `unsafe`. |
| Toolchain identity | Lean 4.34.1, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`; pinned Mathlib checkout clean. |
| Focused Lean build | Passed for the bridge and generated audit module; Lake reported 3,567 jobs, including cached dependencies. |
| Warnings treated as errors | Both `ConnesSpectralTripleBridge.lean` and `SouriauKillingLipschitzBridge.lean` passed `lean -DwarningAsError=true`. |
| Transitive Lean axiom audit | All 39 inventoried declarations passed. The union of reported axioms is exactly `propext`, `Classical.choice`, and `Quot.sound`. |

The focused build replayed pre-existing warnings in unchanged imports. The
two affected mathematical owners passed their separate warning-as-error
checks. The reproducible commands are in the focused package's README.

### Verified source fingerprints

| Source | SHA-256 |
| --- | --- |
| `ConnesSpectralTripleBridge.lean` | `cce2e8d37feaba610437407fb3f1d2d67be1354c584ae2a402bc43b12d3d3512` |
| `SouriauKillingLipschitzBridge.lean` | `01a219aa48634a92dcacca0503e0b342d84625988039054045214c29fab6d7f9` |
| `SouriauKillingLipschitzBridgeAudit.lean` | `28b15c95bb9c8783d1565d9a94311b62f899a77f6215151143e6707b616ae27f` |

The strict text screen initially flagged the pre-existing data-only
`SpectralTriple` structure because no inhabitant was recognizable in that
same file. A native `Inhabited` instance using the zero Dirac element resolves
that source-screen finding. It asserts inhabitation only, not nondegeneracy or
finite spectral distance. All estimates remain quantified over arbitrary
Dirac elements, and the Souriau adapter uses the actual modular generator.

The declaration-DAG status command could not load `dag-toolchain.json` in
the observed checkout. No live graph freshness or complete graph coverage is
claimed; source definitions, imports, and consumers were inspected directly.

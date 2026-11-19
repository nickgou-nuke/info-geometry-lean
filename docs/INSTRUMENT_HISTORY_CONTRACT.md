# Ordered instrument histories and represented GNS state

**Fresh restoration — 17 November 2026.** This is a new source-grounded
reconstruction of the lost contract. The recovered Lean candidates have been
read; no compilation, audit or gate result is asserted by this document.

## 1. Actual carriers and inputs

The finite-system carrier is `Matrix S S ℂ`, with
`[Fintype S] [DecidableEq S]`. The internal Kraus index `κ` has
`[Fintype κ] [DecidableEq κ]`. Recorded outcomes are specifically `Fin 2`.
The instrument is time dependent:

```lean
ρ : Matrix S S ℂ
K : ℕ → Fin 2 → κ → Matrix S S ℂ
```

The source does not impose stationarity, a product-state form, or commutation
of the system operators. Positivity, normalization and completeness are
separate hypotheses, used only where required:

```lean
hρ : ρ.PosSemidef
htrace : Matrix.trace ρ = 1
hK : ∀ n, (∑ a : Fin 2, ∑ i : κ,
  star (K n a i) * K n a i) = 1
```

The history index at depth `n` is `Fin (2 ^ n)`, with the existing
`stageIndexEquiv n : Fin (2 ^ n) × Fin 2 ≃ Fin (2 ^ (n + 1))`.
Do not replace it with an unproved abstract process or an arbitrary alphabet.

## 2. Ordered branch construction

`historyWord` appends the selected family `K n a` to the earlier word.
`branchState` applies the existing `forwardWord` to `ρ`.
Its successor theorem has the actual order

\[
B_{n+1,(h,a)}=\sum_{i\in\kappa} K_{n,a,i}B_{n,h}K_{n,a,i}^{\dagger}.
\]

Thus later operations act after earlier ones; internal labels are summed
inside the existing Kraus map. The empty word gives `B₀=ρ`.
Branch positivity follows from `hρ` without requiring completeness.
No commutative reduction is used in this system propagation.

## 3. Weights, marginals and normalization

Define the complex history weight by the ordinary matrix trace
`pₙ(h) = Matrix.trace (branchState ρ K n h)`.
From positive branches prove `0 ≤ pₙ(h)` in `ComplexOrder` and
`pₙ(h).im = 0`. The empty-history weight is `trace ρ`, not an
independently postulated constant.

Completeness proves the prefix law
`∑ a : Fin 2, pₙ₊₁(h,a) = pₙ(h)` and hence
`∑ h : Fin (2^n), pₙ(h) = trace ρ` at every depth.
Trace-one input therefore yields normalized probabilities.
These marginal and total-trace identities do not need `hρ`.
Ordinary trace is used throughout; no extra factor `2⁻ⁿ` is inserted.

## 4. Full pointer matrices and compatibility

Define `historyDensity ρ K n = Matrix.diagonal (historyWeight ρ K n)`
on the existing full `MatrixStage n` carrier.
This is the selected dephased pointer density. It is positive under `hρ`
and has trace `trace ρ` under `hK`.
After the actual `stageIndexEquiv` reindexing, ordinary partial trace over
the newest binary factor recovers the previous density.

Define the complex linear functional on every full matrix observable by

\[
\Omega_n(X)=\operatorname{Tr}(X D_n)
            =\sum_h X_{hh}p_n(h).
\]

The diagonal formula follows from the specified density; it does not assert
that the observable algebra is diagonal or that arbitrary quantum histories
must be dephased. Prove positivity for every positive semidefinite full `X`
and `Ωₙ(1)=trace ρ`. For the existing concrete successor embedding
`X ↦ X ⊗ I₂`, prove `Ωₙ₊₁(concreteStep n X)=Ωₙ(X)`.
Then prove the restriction law for every existing `concreteMap hij`.

## 5. Native carrier transport and GNS construction

The second owner uses native
`CStarMatrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ`.
`StarAlgEquiv.arrowCongr` transports the existing concrete maps through
`CStarMatrix.ofMatrixStarAlgEquiv`; identity, composition and matrix readback
are established. No second raw matrix tower is introduced.

Transport the actual history linear functional, prove its C⋆ positivity,
and construct the positive functional and the existing repository
`CStarStateColimit.Native.State` wrapper: a native positive linear map with
unit normalization.
Construct `cstarHistoryStateFamily` using the proved restriction law.
Then instantiate the existing filtered GNS `representedVacuumState` at stage
zero on `representedCStarClosure`, the norm closure of its represented
algebraic colimit. Recover every full finite-stage functional exactly.

`representedHistoryState_unique` compares states on this same represented
closure and assumes equality on every `n` and every full stage observable.
Its proof uses dense range and continuity. This is not uniqueness from
diagonal outcome probabilities alone, nor uniqueness on an unspecified
ambient completion. No faithful representation, traciality, KMS property,
UHF identification, von Neumann factor type or tail property is asserted.

## 6. Reuse and validation boundary

The finite owner imports the existing `KrausBoundaryDuality`, focused
`FinitePartialTrace`, and `CuntzMatrixTraceTower` owners.
The GNS owner imports that finite owner, native `CStarMatrix`, and existing
`FilteredGNSVacuumState`. The generic State/GNS owners remain unchanged.
Expected source counts are 18 theorems / 5 definitions in `InstrumentHistory`
and 7 theorems / 6 public definitions in `InstrumentHistoryGNS`, plus
3 private instance-family abbreviations and 2 local instances.
Fresh kernel checking, all-declaration axiom auditing and independent source
review must precede acceptance. A matching recovery hash is source recovery
evidence, not a replacement for those checks.

# Unbounded Modular Machinery: Repo-Native Translation (Krein / Doubled / Hestenes)

## Executive statement

The previous chapters sealed the bounded/regularized lane well.
This chapter translates the **unbounded** payload explicitly into repo-native language.

Core correction:

- bounded surrogate lane: projector-controlled regular block (`Preg`) + bounded functional calculus;
- canonical unbounded lane: affiliated modular operator, spectral support projection, unbounded logarithmic generator.

The translation must keep both lanes distinct and then provide the identification bridge.

## 1. Canonical unbounded objects (not optional)

In genuine modular theory, the primitive objects are:

1. relative modular operator `Δ` (positive self-adjoint, generally unbounded),
2. support projection `s(Δ) = 1_(0,∞)(Δ)`,
3. modular Hamiltonian `K = -log Δ` defined by spectral calculus on support.

Key fact:
`K` is typically unbounded.

So the correct statement is not "bounded away from zero", but:

- zero eigenspace removed by support restriction,
- possibly arbitrarily small positive spectrum remains,
- logarithm is well-defined but unbounded (affiliated operator).

## 2. Repo-native expression on doubled carrier

On the doubled real carrier `H₂ := DoubledSpace E`, we keep:

- internal phase axis `K_axis := J ∘ ε`,
- projector package for support handling in implementation lanes,
- generator/readout transport contracts as typed morphism evidence.

Unbounded translation doctrine:

1. canonical support is spectral (`s(Δ)`),
2. implementation support may be realized via Drazin/MP package (`Preg/Pzero` etc.),
3. identification is a theorem target, not an axiom.

## 3. What projector package does in the unbounded story

The projector package remains operationally load-bearing, but with proper scope:

- It gives computable/algebraic support realizations in surrogate lanes.
- It does **not** define the logarithm.
- The logarithm is still defined spectrally on the canonical support.

So the right sentence is:

> log is spectral; projectors realize support routing for executable lanes.

This keeps the repo architecture current (Native Closure Mandated) in Type III-facing directions.

## 4. Unbounded-correct analogue of the Penrose boundary

In geometric compactification:
boundary is finite after conformal compression, preserving causal order.

In unbounded modular translation:
boundary is support boundary (`ker Δ` versus `s(Δ)`), preserving generator admissibility.

Operational interior is:

- geometric lane: causal diamond interior,
- operator lane: support-restricted affiliated-generator domain.

So the Operator Penrose analogue survives, but only with this refinement:

- "finite regular block" in bounded surrogates,
- "affiliated support-restricted unbounded generator" in canonical lane.

## 5. Theorem targets required for truthful closure

To lift from architecture to one coherent theorem package, the following targets are required.

### T1. Support-restricted logarithm exists canonically

Schematic:

```lean
theorem supportRestrictedLog_exists
  (Δ : UnboundedPositiveSelfAdjoint H₂) :
  ∃ K : AffiliatedSelfAdjoint H₂,
    K = -log_on_support Δ
```

### T2. Surrogate projector agrees with spectral support under current (Native Closure Mandated) hypotheses

Schematic:

```lean
theorem preg_eq_spectralSupport_of_selfAdjoint_limit
  (Δ̂ : SurrogateModularOperator H₂) :
  current (Native Closure Mandated)y_hypotheses Δ̂ ->
  Preg Δ̂ = spectralSupport (limitOperator Δ̂)
```

### T3. Connes cocycle generator compatibility

Schematic:

```lean
theorem cocycle_generator_on_support
  (φ ψ : FaithfulState) :
  generator (Dψ:Dφ) = supportRestrictedLog (Δ ψ φ)
```

### T4. Intertwiner/readout coherence across lanes

Schematic:

```lean
theorem unbounded_readout_preserved
  (F : Intertwiner operatorLane causalLane) :
  preserves_support F ∧ preserves_generator F ∧ preserves_readout F
```

These are the minimal informative targets for a truthful unbounded closure.

## 6. Lean strategy (current ecosystem reality)

Given present `mathlib` boundaries, the practical route is staged:

1. Keep finite/bounded executable lane as current trunk.
2. Introduce typed interfaces for unbounded affiliated objects and domains.
3. Prove approximation/consistency theorems from surrogate package to canonical interfaces.
4. Reserve full Type III/global modular closure as a higher owner program.

This preserves compile-time progress without making false global claims.

## 7. Strict guardrails for writing and proving

1. Never equate "projector support" with canonical support without hypotheses.
2. Never claim boundedness of `-log Δ` in unbounded lane.
3. Always separate:
   - canonical spectral definition,
   - surrogate algebraic realization.
4. Keep `Δ-first` discipline:
   support -> logarithm -> generator -> flow -> scalar/readout shadow.

## 8. Final translation sentence

> The unbounded machinery in this repo should be read as a two-lane doctrine:
> canonical modular support/log calculus defines truth; the Drazin/MP projector package provides executable support routing. Closure is obtained only when a proved identification theorem connects the two.


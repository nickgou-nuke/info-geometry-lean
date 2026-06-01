# Induction Systematics in InfoGeometry

> Status: maintained local guide
> Audited: 2026-05-30
> See: [../README.md](../README.md), [README.md](README.md), [../skills/induction-systematics/SKILL.md](../skills/induction-systematics/SKILL.md)

This guide explains the induction patterns that are actually formalized in the
codebase. It is a navigation document, not proof authority. Lean source remains
the authority.

## Core idea

In this repository, induction is always a **transport rule**:

- a base case;
- a one-step preservation lemma;
- an explicit recursive or categorical carrier;
- a theorem that packages the finite iteration.

The same shape appears in ordinary `Nat` induction, structural recursion,
strong induction, finite-stage algebraic towers, and algebraic direct limits.

## The induction families used here

| Family | Lean shape | Typical files |
| --- | --- | --- |
| Ordinary `Nat` induction | `induction n with | zero => ... | succ n ih => ...` | `lean/InfoGeometry/Meta/EssenceOfInductiveProof.lean`, `lean/InfoGeometry/Meta/InductionHandbook.lean` |
| Generalized induction | `induction n generalizing m k with` | `lean/InfoGeometry/Meta/InductionHandbook.lean` |
| Strong induction | `Nat.strong_induction_on` or a derived strong-induction theorem | `lean/InfoGeometry/Meta/InductionHandbook.lean`, `lean/InfoGeometry/Meta/EssenceOfInductiveProof.lean` |
| Structural induction | `induction xs with`, `induction t with` | `lean/InfoGeometry/Meta/InductionHandbook.lean` |
| Recursor/termination-based recursion | `Nat.rec`, `List.rec`, `termination_by` | `lean/InfoGeometry/Meta/InductionHandbook.lean` |
| Mutual recursion | `mutual ... end` | `lean/InfoGeometry/Meta/InductionHandbook.lean` |
| Finite-stage transport | one-step algebra homomorphism + `∀ n` by induction | `lean/InfoGeometry/Algebra/InductiveSuperClosureLemmas.lean`, `lean/InfoGeometry/Algebra/FiniteInductiveSUSY.lean` |
| Image-local infinite transport | finite-stage closure pushed through `Stage n →+* Limit` | `lean/InfoGeometry/Algebra/InfiniteSuperClosureLemmas.lean` |
| Algebraic direct limit | `DirectedSystem`, `DirectLimit`, canonical injections, compatible cones | `lean/InfoGeometry/Algebra/DirectLimitSuperClosureLemmas.lean`, `lean/InfoGeometry/Canonical/SplitCliffordDirectLimit.lean` |
| Tensor-algebra induction | `TensorAlgebra` functoriality + stagewise transport | `lean/InfoGeometry/Algebra/TensorAlgebraInduction.lean`, `lean/InfoGeometry/Algebra/TensorAlgebraCanonical.lean` |
| Iterative exponentiation | primitive recursion for finite powers/products/orbits | `lean/InfoGeometry/Algebra/IterativeExponentiation.lean` |
| Nilpotent finite product limits | finite product induction plus eventually-constant `Tendsto` | `lean/InfoGeometry/Algebra/NilpotentFiniteProductLimit.lean`, `lean/InfoGeometry/Clifford/SplitQuaternionNilpotentFlow.lean` |
| Tower/trajectory induction | recursive stage trajectory plus invariant transport | `lean/InfoGeometry/Meta/EssenceOfInductiveProof.lean`, `lean/InfoGeometry/Meta/InductionHandbook.lean` |

## Category-language reading

The repo uses category language in the practical sense of **diagrams, cones,
and colimits**.

The main pattern is:

- `Stage : ℕ → Type*` is a staged diagram;
- `bond n : Stage n →+* Stage (n + 1)` is the transition map;
- `bondMap bond m n h` is the iterated arrow between stages;
- `DirectedSystem Stage ...` packages the functorial laws;
- `DirectLimit Stage ...` is the algebraic colimit;
- `directLimitOf bond n` is the canonical injection of stage `n`;
- `CompatibleCone bond toLimit` is the cone condition into an external target;
- `directLimitLift bond toLimit hcone` is the universal map out of the colimit.

This is the theorem-safe way the codebase talks about “limit” behavior.
It is algebraic and categorical; it is not a topological completion unless a
separate topology file proves that extra structure.

## Canonical proof shape

Most induction proofs in the codebase follow one of these templates.

### 1. Base + step

```lean
intro n
induction n with
| zero => exact h0
| succ n ih =>
    -- use one-step lemma here
    exact hstep n ih
```

This is the standard finite-stage rule.

### 2. Strengthen the statement first

If the induction hypothesis needs extra parameters, generalize them before the
`induction`.

```lean
induction xs generalizing ys with
| nil => ...
| cons x xs ih => ...
```

### 3. Prove the one-step lemma, then iterate

This is the main bridge style for superclosure and tower transport:

- prove the successor-preservation lemma once;
- use ordinary induction to get `∀ n`;
- only then transport into a target image or direct limit.

### 4. Use a recursive trajectory when the object is defined recursively

The repo often packages the carrier as a trajectory:

- `recursiveTrajectory` in `EssenceOfInductiveProof.lean`;
- `coneTrajectory` / `stageTrajectory` in `InductionHandbook.lean`.

Then the theorem states that the invariant holds at every recursive stage.

### 5. Use `DirectLimit` only when there is a real tower

If the object is genuinely staged, use the algebraic direct limit:

- build the bonds;
- prove the directed-system laws;
- define the canonical maps;
- prove compatibility with the bonding maps;
- use the universal lift only after the cone condition is proved.

## Current owner files

Read these first when working on induction-heavy proofs:

- `lean/InfoGeometry/Meta/EssenceOfInductiveProof.lean`
- `lean/InfoGeometry/Meta/InductionHandbook.lean`
- `lean/InfoGeometry/Meta/FiniteToInfiniteTransitionSOP.lean`
- `lean/InfoGeometry/Algebra/InductiveSuperClosureLemmas.lean`
- `lean/InfoGeometry/Algebra/InfiniteSuperClosureLemmas.lean`
- `lean/InfoGeometry/Algebra/DirectLimitSuperClosureLemmas.lean`
- `lean/InfoGeometry/Algebra/TensorAlgebraInduction.lean`
- `lean/InfoGeometry/Algebra/TensorAlgebraCanonical.lean`
- `lean/InfoGeometry/Algebra/IterativeExponentiation.lean`
- `lean/InfoGeometry/Algebra/NilpotentFiniteProductLimit.lean`
- `lean/InfoGeometry/Clifford/SplitQuaternionNilpotentFlow.lean`
- `lean/InfoGeometry/Algebra/FormalSeriesCalculus.lean`
- `lean/InfoGeometry/Algebra/FinsuppN2ModeInduction.lean`
- `lean/InfoGeometry/Algebra/FiniteInductiveSUSY.lean`
- `lean/InfoGeometry/Algebra/InfiniteN2ModeInduction.lean`
- `lean/InfoGeometry/Canonical/FiniteInvariantTransport.lean`
- `lean/InfoGeometry/Canonical/SplitCliffordDirectLimit.lean`
- `lean/InfoGeometry/Clifford/Cl11TensorTower.lean`
- `lean/InfoGeometry/Clifford/Cl11TensorTowerIteration.lean`

## What to prove first

For any induction-heavy theorem, prove these in order:

1. the seed case;
2. the one-step transport lemma;
3. the finite-stage `∀ n` theorem;
4. the image-local theorem, if there is a target;
5. the direct-limit theorem, only if there is a real tower;
6. the completion theorem, only if topology and convergence are formalized.
   For operator definitions given by recursion/iteration, use the inductive
   formula directly; for formal exp/log/geometric series, use the algebraic
   `PowerSeries` lane coefficientwise; do not default to analytic completion.

## Iterative exponentiation, not Taylor series

The primary finite exponentiation lane is primitive recursion:

```text
x^0       = 1
x^(n + 1) = x^n * x
```

Owner:

- `lean/InfoGeometry/Algebra/IterativeExponentiation.lean`

Important declarations:

- `inductivePower`
- `inductivePower_eq_pow`
- `inductivePower_add`
- `map_inductivePower`
- `iterativeProduct`
- `iterativeProduct_const`
- `map_iterativeProduct`
- `iterativeOrbit`
- `iterativeOrbit_unique`
- `invariant_iterativeOrbit`

This is not an infinite sum.  Each exponent is a finite iterate, and invariants
are proved by induction on the exponent.  Taylor/power series are separate
formal or analytic encodings of functions; they are not the primitive finite
power operation. Historically, exponential/logarithmic laws were developed
through iteration, inversion, compound-interest, and differential-equation
laws before Taylor-series presentation became standard.

For nilpotent normalized products, use
`lean/InfoGeometry/Algebra/NilpotentFiniteProductLimit.lean`:

- `recursive_prod`
- `recursive_sum`
- `nilpotent_prod_induction`
- `finite_prod_seq_val`
- `finite_to_infinite_limit`

Here the `Tendsto` theorem is safe because the normalized nilpotent sequence is
eventually constant at `1 + T • N`. It is not a proof of a general analytic
completion or an external Virasoro/Dirac exponential flow.

The split-quaternion/Hestenes-style coordinate realization is in
`lean/InfoGeometry/Clifford/SplitQuaternionNilpotentFlow.lean`. It uses the
existing `SplitQuaternion` model, proves `(i - j)^2 = 0`, and states convergence
with an explicit coordinatewise predicate `sq_tendsto` rather than pretending a
full topological Clifford algebra has been constructed. The companion file
`lean/InfoGeometry/Clifford/SplitQuaternionFlowCoordinates.lean` records the
norm-one coordinate curves for elliptic, hyperbolic, and parabolic examples;
this is not an exhaustive subgroup classification.

The `Cl(1,1)` matrix tensor tower uses the same finite-iteration principle:

- `iteratedStageEmbed m k` is the `k`-fold finite advance by `A ↦ A ⊗ₖ I₂`;
- `iteratedStageEmbed_pow` preserves finite powers;
- `iteratedStageEmbed_superBracket` preserves finite superbrackets;
- `ofStage_iteratedStageEmbed` identifies finite iterates in the algebraic direct limit.

## Definitional formal series, not analytic completion

There is a separate algebraic lane where `exp`, `log`, or geometric-series
symbols are treated as elements of `PowerSeries A` rather than analytic
functions.

- `formalExp`
- `formalLogOnePlus`
- `formalGeometric`
- `coeff_formalExp`
- `coeff_formalLogOnePlus`
- `coeff_formalGeometric`
- `map_formalExp`
- `map_formalLogOnePlus`
- `map_formalGeometric`
- `formalGeometric_mul_one_sub_X`

In that lane, each coefficient calculation is finite, because multiplication in
`PowerSeries A` uses the finite Cauchy-product formula at each coefficient.

The firewall is:

```text
PowerSeries identity           → algebraic formal-series theorem
coefficient calculation        → finite coefficientwise proof
map of formal series           → coefficientwise ring/algebra-map theorem
evaluation at a non-formal x   → separate substitution/evaluation hypotheses
analytic equality of functions → only with topology/convergence theorems
```

So replacing `exp`/`log` by formal series is honest when the theorem is about
formal coefficients or formal algebra. It is not, by itself, an analytic
completion statement.

## What not to do

- Do not call a finite-stage theorem an infinite limit.
- Do not hide missing limit logic in a certificate, witness, or wrapper field.
- Do not replace a direct-limit theorem with a prose claim.
- Do not treat `Finsupp` as a topological completion.
- Do not replace an inductive operator formula with an analytic completion story.
- Do not claim a categorical colimit unless `DirectLimit` and its maps are actually built.

## Where this shows up in the codebase

Typical downstream surfaces:

- supergraded closure transport;
- finite N=2 / SUSY chains;
- tensor-algebra functorial transport;
- split Clifford towers;
- direct-limit image compatibility;
- recursive seed-and-step invariant packets.

If you need to formalize a new induction corridor, start from the weakest honest
pattern that fits the mathematics.

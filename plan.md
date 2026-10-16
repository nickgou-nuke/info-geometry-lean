# RH and Hodge Formalization Bridge Plan

## Purpose and scope

Connect existing arithmetic and rational cycle-span results through small,
kernel-checked bridge theorems. This plan formalizes the *vicinity* of the
Riemann-hypothesis and Hodge-conjecture arguments; it does not assume either
conjecture, claim either is proved, or encode the reported (7/8) zero-free
region or CM Hodge theorem as an established result.

The codebase is the authority for carriers and theorem statements. Before each
implementation step, search the repository for existing definitions and
dependents and reuse their owners. In particular, do not create parallel
Möbius, zeta, Hodge-space, or cycle-class APIs merely to fit this plan.

## Existing owner neighborhood

### Arithmetic side

- `lean/InfoGeometry/Arithmetic/ActualRiemannZetaMobiusLSeriesBridge.lean`:
  Mathlib-backed Möbius Dirichlet-series reciprocal identities on
  `1 < s.re`.
- `lean/InfoGeometry/Arithmetic/MobiusFiniteAbelSummation.lean`:
  finite summation by parts, including the Möbius/Mertens specialization.
- `lean/InfoGeometry/Arithmetic/PrimeBitFiniteMobiusPolynomial.lean`,
  `MobiusFourierLocalMoment.lean`, `MobiusFourierPaperReadout.lean`, and
  `MobiusFourierFiniteAbelBridge.lean`: finite prime-bit/Möbius polynomial
  readouts, its value at the origin as the Mertens sum, and finite Fourier
  summation by parts.
- `lean/InfoGeometry/Arithmetic/TrigonometricPolynomialLocalMomentBound.lean`,
  `LocalMomentToPointValue.lean`, and
  `MobiusFourierTrigonometricBridge.lean`: finite derivative/persistence
  bounds and conditional finite-interval moment lower bounds. These are not
  asymptotic moment estimates.
- `lean/InfoGeometry/Arithmetic/MobiusMertensRHEquivalence.lean`:
  finite Mertens recurrence and prime-bit/Möbius readouts, plus an explicit
  open interface around the RH-related asymptotic edge.
- `lean/InfoGeometry/Arithmetic/RiemannZetaEvidenceCorridor.lean` and
  `lean/InfoGeometry/Arithmetic/RiemannHypothesis.lean`: existing analytic
  zeta facts, symmetry/readouts, finite spectral material, and certificate
  interfaces. Inspect their exact declarations before adding any bridge.
- `lean/InfoGeometry/Arithmetic/RiemannZetaFiniteFacts.lean`: Mathlib-backed
  nonvanishing on `1 ≤ s.re` and functional-equation reflection consequences.
- `lean/InfoGeometry/Spectral/RiemannWeilTrace.lean`: finite prime-phase and
  spectral-mode identities; this is not the full explicit formula.

The source search found a declaration named
`zero_free_region_from_dirichlet_bounds` in
`lean/InfoGeometry/Arithmetic/ExplicitFormula.lean` whose premise assumed the
identical region stated in its conclusion. It had no other source usages in
the inspected tree, so that tautological declaration has been removed from
the current worktree. The owner still contains other assumption-driven
explicit-formula readouts; inspect their exact contracts before relying on
them.

### Hodge and cycle side

- `lean/InfoGeometry/HodgeCohomology/RationalCycleSpan.lean`: generic
  ℚ-linear span, surjectivity, and dual-detection results. It does not itself
  define cohomology of a CM abelian variety or algebraic cycle classes.
- `lean/InfoGeometry/Canonical/RationalHodgeSectorIntertwiner.lean`,
  `DegreeAwareRationalHodge.lean`, and `TopologicalRationalHodge.lean` are
  additional rational-sector/Hodge-star infrastructure. Inspect their exact
  carriers before attempting to connect them to geometric cycle classes.
- `lean/InfoGeometry/Canonical/DiscreteRationalHodgeConjugation.lean` models
  a finite rational incidence cochain complex and an explicitly supplied
  linear equivalence called `star`; it does not supply a complex variety's
  Hodge decomposition. `FiniteHarmonicRepresentative.lean` is finite
  dimensional real linear algebra. Neither currently provides the CM
  algebraic-cycle map required by the proposed Hodge chain.

## Causal dependency graph

```text
ARITHMETIC
finite Möbius convolution and finite Abel summation
        │
        ├──> exact finite weighted-sum identities
        │             │
        │             └──> conditional estimate interface for M(N)
        │                              │
        └──> zeta × Möbius-LSeries = 1 on Re(s) > 1
                                       │
                         separately proved analytic transfer lemma(s)
                                       │
                          explicitly stated zero-free-region target

HODGE / CYCLES
existing rational Betti carrier and comparison map
        │
        ├──> define/identify the rational (p,p) subspace
        │
        └──> define algebraic-cycle index and cycle-class map
                         │
             cycle classes land in the (p,p) subspace
                         │
       span/surjectivity or dual-detection criterion (reuse RationalCycleSpan)
                         │
      CM-specific construction/representation theorem, if its prerequisites
      are supplied and independently proved
```

The two branches remain mathematically separate unless an actual map between
their carriers is found and proved. A shared use of words such as “spectrum,”
“cycle,” or “zeta” is not such a map.

## Work phases

## Ground-truth progress update

Repository search has already located the proposed finite arithmetic
interconnections: the prime-bit/Möbius polynomial has an exact finite
integer-cutoff readout; its Fourier value at zero is the Mertens sum; finite
Abel summation rewrites the Fourier sum through Mertens prefixes; and finite
Lipschitz persistence yields conditional finite-interval moment lower bounds.
These existing owners should be audited and reused, not reimplemented.

The next legitimate RH-chain gap is beyond these finite identities: a proved
analytic transfer from a quantitative Mertens/Fourier estimate to a specified
zero-free region. No such transfer was established by this search. The CM
Hodge chain likewise still needs geometric cycle-class and CM-action carriers;
the generic rational span criterion is not that construction.

Consequently, do not add a forwarding theorem merely to connect two existing
readouts. First produce and adversarially check a precise missing theorem
contract with all analytic/geometric hypotheses identified. If no
non-vacuous contract follows from current owners and Mathlib, leave that edge
open and record the obstacle instead of encoding the desired conclusion as
input data.

### Phase 0 — Ground truth and theorem contracts

1. Read the current canonical pipeline, hive commandments, categorical map,
   and deep-search protocol.
2. Inspect the owner declarations and all imports/dependents listed above;
   search for existing candidates for each proposed statement.
3. Record exact carriers, scalar fields, domains, conventions, and theorem
   hypotheses. Distinguish proved declarations from open interfaces and
   certificate projections.
4. Write a Gate 2 counterexample checklist before committing to any claim:
   boundary values, zero terms, empty/finite cases, rationality, and direction
   of each implication.

**Exit condition:** a reviewed statement ledger with no theorem inferred from
its name or docstring alone.

### Phase 1 — Reusable arithmetic bridge

1. Reuse the existing finite Möbius convolution identities and finite Abel
   summation theorem; add no duplicate definitions.
2. Prove only concrete finite consequences needed by a later analytic owner,
   such as a weighted finite sum rewritten in terms of Mertens prefix sums.
3. State any growth estimate as an explicit hypothesis on the existing
   `mertensFunction`; do not manufacture it from finite computations.
4. Connect the Dirichlet-series identity only on its currently justified
   half-plane `1 < s.re`.

**Exit condition:** every theorem is unconditional where the source is
unconditional, and conditional estimates remain visibly conditional.

### Phase 2 — Analytic transfer boundary

1. Inspect Mathlib and repository owners for the exact summation/Dirichlet
   transfer theorems required. Do not replace them with a hand-written
   assertion or an informal “standard argument.”
2. State a narrow transfer theorem with explicit convergence and growth
   hypotheses, only if all prerequisites can be represented by existing
   Mathlib objects and proved lemmas.
3. Keep analytic continuation, smoothing, twisted sums, Poisson summation,
   and zero-free conclusions as separate obligations. The transcript's
   six-phase family and (7/8) bound are targets for investigation, not inputs.
4. If the necessary theorem is not available or provable from the current
   owners, stop at a precise open mathematical contract; do not encode it as
   a “certificate” that hides the missing proof.

**Exit condition:** no zero-free-region theorem is stated unless its full
analytic bridge is kernel-proved with the correct domain and boundary.

### Phase 3 — Generic rational cycle-span bridge

1. Search existing cohomology and cycle-class owners before defining anything.
2. Identify the actual rational carrier, comparison/type map, target
   ((p,p))-subspace, cycle indices, and cycle-class linear map.
3. Prove that cycle classes land in the target subspace using the actual
   geometric definitions, then apply the reusable span/surjectivity or
   dual-detection result from `RationalCycleSpan`.
4. Keep the resulting statement generic until an actual variety-specific
   carrier and cycle map are present. Do not call a generic span theorem the
   Hodge conjecture.

**Exit condition:** the output is a correctly typed cycle-span criterion over
ℚ, with no unstated geometric assumptions.

### Phase 4 — CM-specific interface and construction

1. First locate or formalize the relevant abelian-variety, rational
   cohomology, Hodge decomposition, CM action, and algebraic-cycle owners.
2. Represent the four-factor type-balance/exchange mechanism only after its
   tensor carriers and conjugation actions are defined and verified.
3. Treat auxiliary varieties, correspondences, theta classes, and nonzero
   pairing witnesses as separate construction lemmas with explicit owners.
4. Formalize any Hecke/Frobenius compatibility needed to identify rational CM
   structures; complex-form existence alone is insufficient.
5. Derive a CM-family cycle-span theorem only from these proved constructions.
   State its exact scope; do not generalize to all abelian or smooth projective
   varieties without a proved reduction.

**Exit condition:** every CM-specific premise is a genuine definition or
proved theorem, and the result's scope matches those premises.

### Phase 5 — Independent review and closure

For every new owner file:

1. Keep one mathematical owner per substantive definition/theorem and reuse
   existing Mathlib/repository APIs.
2. Run the static OpenGauss/QMS preflight, then independent adversarial review
   of theorem meaning, edge cases, and non-vacuity.
3. Compile only through the repository's sequential locked build route after
   verifying no compiler task is active.
4. Check `#print axioms` for all headline and bridge declarations; reject
   `sorryAx`, custom axioms, fake witness/certificate wrappers, vacuous
   hypotheses, and unsupported interpretations.
5. Record exact files and theorem names covered by the audit. A clean local
   build is not evidence for claims outside the declarations checked.

## Explicit non-goals

- Proving RH, a quasi-RH statement, or any fixed zero-free boundary by
  renaming a certificate interface.
- Proving the general Hodge conjecture or the CM-type case without the
  corresponding geometric constructions.
- Treating numerical evidence, a video description, a paper announcement, or
  a finite spectral analogy as a Lean proof.
- Identifying the arithmetic and Hodge branches without a proved carrier map.
- Passing to any continuum by analytic rhetoric; any limit construction must
  use the repository's categorical colimit owners when mathematically
  applicable.

## Deliverable ledger

Maintain a table during implementation with columns:

| Claim / Lean declaration | Existing owner reused | New owner, if needed | Status | Remaining hypotheses |
|---|---|---|---|---|
| Finite summation by parts: `MobiusFiniteAbelSummation.finite_summation_by_parts` | `MobiusFiniteAbelSummation` | none | statement audited | `CommRing R`; finite `N`; no limit or growth claim |
| Möbius/Mertens complex finite sum: `mobius_sum_eq_mertens_summation_by_parts_complex` | `MobiusFiniteAbelSummation`, `MobiusMertensRHEquivalence.mertensFunction` | none | statement audited | finite `N`; does not supply Mertens growth |
| Zeta–Möbius inverse: `ActualRiemannZetaMobiusLSeriesBridge.actualRiemannZeta_mul_mobius_LSeries_eq_one` | Mathlib Dirichlet `LSeries` and this bridge owner | none | statement audited | `1 < s.re`; no continuation or RH consequence |
| Möbius partial-sum integral representation: `ActualRiemannZetaMobiusLSeriesBridge.mobius_LSeries_eq_partial_sum_integral_of_one_lt_re` | Mathlib `LSeries_eq_mul_integral'`, `ArithmeticFunction.abs_moebius_le_one` | same bridge owner | proved and kernel-checked | `1 < s.re`; uses absolute convergence; makes no claim at or left of `Re(s)=1` |
| Reciprocal-zeta Mertens integral: `ActualRiemannZetaMobiusLSeriesBridge.one_div_actualRiemannZeta_eq_mertens_integral_of_one_lt_re` | preceding integral theorem, `MobiusFiniteAbelSummation.mobius_sum_range_eq_Icc_complex` | same bridge owner | proved and kernel-checked | `1 < s.re`; identity on the absolute-convergence half-plane only |
| Mertens partial-sum Abel integral: `LSeries_eq_mul_integral` in `Mathlib/NumberTheory/LSeries/SumCoeff.lean` | Mathlib `AbelSummation` | none | searched | Requires `LSeriesSummable f s`, `∑_{k ∈ Icc 1 n} f k = O(n^r)`, `0 ≤ r < Re(s)` |
| Absolute `LSeriesSummable` below `Re(s)=1` | `ActualRiemannZetaMobiusLSeriesBridge.not_mobius_LSeriesSummable_of_re_le_one`; Mathlib `ArithmeticFunction.LSeriesSummable_moebius_iff` | same bridge owner | kernel-checked impossibility result | Mathlib states absolute summability of the Möbius L-series iff `1 < s.re`; this boundary theorem rules it out when `s.re ≤ 1` |
| Ordered Möbius-series convergence under Mertens square-root cancellation: `MobiusMertensRHEquivalence.mobius_ordered_series_tendsto_of_square_root_cancellation` | `mertens_growth_bound_of_square_root_cancellation`, `mobius_weighted_prefix_bounded_of_mertens_growth`, antitone Dirichlet test | Mertens owner | proved and kernel-checked | assumes `MertensSquareRootCancellation` and real `s>1/2`; this is conditional and does not prove RH |
| Ordered Möbius series under uniformly bounded Mertens prefixes: `MobiusMertensRHEquivalence.mobius_ordered_series_tendsto_of_bounded_mertens` | `mertensFunction_succ`, Mathlib antitone Dirichlet test | Mertens owner | proved and kernel-checked | real `s>0`; assumes a uniform bound on all Mertens prefixes |
| Ordered Möbius series from uniformly bounded weighted prefixes: `MobiusMertensRHEquivalence.mobius_ordered_series_tendsto_of_bounded_weighted_prefix` | Mathlib `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded` | Mertens owner | proved and kernel-checked | real `a<s`; assumes the weighted Möbius prefix sums with weight `(n+1)^(-a)` are uniformly bounded |
| Ordered Möbius prefixes from polynomial Mertens growth: `MobiusMertensRHEquivalence.mobius_weighted_prefix_bounded_of_mertens_growth` | finite summation by parts, mean-value decrement bound for `x ↦ x^(-a)`, Mathlib `Real.summable_nat_rpow` | Mertens owner | proved and kernel-checked | assumes `0 ≤ r < a`, `C ≥ 0`, and `∀ N, ‖M(N)‖ ≤ C (N+1)^r`; derives the uniform weighted-prefix bound |
| Ordered Möbius-series convergence from polynomial Mertens growth: `MobiusMertensRHEquivalence.mobius_ordered_series_tendsto_of_mertens_growth` | preceding weighted-prefix theorem and Mathlib antitone Dirichlet test | Mertens owner | proved and kernel-checked | assumes `0 ≤ r < a < s`, `C ≥ 0`, and `∀ N, ‖M(N)‖ ≤ C (N+1)^r` |
| Global shifted-base polynomial Mertens bound from square-root cancellation: `MobiusMertensRHEquivalence.mertens_growth_bound_of_square_root_cancellation` | Mathlib `IsBigO` eventual bound plus finite-prefix enlargement | Mertens owner | proved and kernel-checked | assumes `MertensSquareRootCancellation`; for each `r>1/2`, produces `C≥0` with `∀N, ‖M(N)‖≤C(N+1)^r` |
| Prime-bit squarefreeness/parity readouts | `PrimeBitMobiusParityBridge.primeBitInteger_squarefree`, `PrimeBitMobiusParityBridge.mobius_primeBitInteger_eq_parity_sign` | existing owner | proved and kernel-checked | used directly; removed the redundant proposition-field bridge bundle |



| Mertens square-root cancellation / genuine RH connection | `MertensSquareRootCancellation`, `RiemannHypothesisProjectiveFormulation.RiemannHypothesisCriticalLine` | analytic transfer theorem not identified | open; no bridge bundle retained | equivalence between Mertens cancellation and the actual nontrivial-zeta-zero condition is unproved; the unrelated arbitrary-function Fredholm certificate surface was removed |
| Generic cycle-span containment/surjectivity/dual obstruction/finite-rank test | `RationalCycleSpan.cycle_span_le_type_subspace`, `cycle_map_surjective_iff_span`, `cycle_map_surjective_iff_dual_detection`, `cycle_map_nonsurjective_iff_dual_obstruction`, `cycle_map_surjective_iff_finrank_span` | none for abstract linear algebra | kernel-checked | non-surjectivity yields a nonzero rational functional annihilating every supplied class; finite-dimensional surjectivity is equivalent to full Betti finrank; concrete rational Betti carrier, comparison, type subspace, and cycle-class map still required |
| Concrete CM algebraic cycles into rational `(p,p)` cohomology | no matching owner found in searched Lean tree; nearby `RealBoundaryHomologyQuotient.RealBoundaryOperator.cycleClass` is real homology only | CM variety, rational cohomology, comparison/Hodge subspace, and algebraic-cycle class owners | open | actual variety-specific carriers and proof that cycle classes land in `(p,p)` are absent from the located owner set |


`independently audited`, or `open`. Do not label a claim “certified” based on
planning, prose, or an interface alone.

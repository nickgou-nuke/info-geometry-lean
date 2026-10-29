# Peirce reflection, native Cartan triples, and algebraic colimit

## Exact scope and intake

Basis: the two 2026-10-28 uploaded streams named in `provenance.json`.
Repository base: `d23c9afe00275126fd4d4e25cb0842ee55fe82af`.
These streams are mathematical intake, not compiler evidence. Their labels
"verified", "reflection positivity", and "mass-gap persistence" are not
accepted merely because they appear in the input.

The ambient carrier is an arbitrary associative unital ring, with a star
operation where stated. All new concrete geometry uses full `Matrix n n ℝ`.
There is no commutativity assumption, diagonal reduction, or complexification.

## Reused owners

* `Core.PeirceDecomposition`: `component10`, `component01` and complements.
* `Core.PeirceGrading`: `reflection p = 2*p-1`, its square/star laws, and corner
  nilpotency. No second Peirce carrier is introduced.
* `Core.DualSeedPeirce.IsDualSeedPair`: precisely `d*d=0`, `b*b=0`,
  `d*b*d=d`, `b*d*b=b`; its existing supports and products are retained.
* Mathlib `IsSl2Triple`: the actual native triple, including `h_ne_zero`.
* Mathlib root `DirectLimit`: the directed quotient with noncommutative ring
  structure, component inclusions, injectivity theorem and universal lift.

`Canonical.SplitCliffordDirectLimit` was inspected and already constructs a
real split-Clifford tower using this root `DirectLimit`. The generic new
colimit results do not replace that tower. This patch does not add a dedicated
split-Clifford adapter or claim to have rebuilt that owner's import closure.
The inspected `TensorTowerColimit` is explicitly finite/staged and the
`UHFInductiveColimitBoundary` model is diagonal/complex; neither is substituted
for the requested full noncommutative carrier.

## Source-derived claims and explicit repairs

1. Stream XLIV: retain `Θ(x)=S*star(x)*S` and the reflected-corner identities.
   Prove multiplication-order reversal and involutivity separately. The
   negative reflected anticommutator equals `N*star(N)+star(N)*N`.
   The other pairing printed in the source, `star(Θ(N))*N`, is instead zero
   because `N*N=0`. Its trace is zero as well. No OS state is constructed.
2. Stream XLV: retain the two reflection-weight equations. From the existing
   reflexive square-zero seed contract, prove the exact native Cartan triple
   only after adding the explicit nonzero-seed hypothesis. Derive support
   idempotence/nonvanishing, the integral Casimir identity and the completed
   involution. The source's reflexivity equations are hypotheses, not results
   valid for every arbitrary opposite-corner pair.
3. Streams XLVI-XLVIII: arbitrary ring homomorphisms preserve the polynomial
   equations. Nonvanishing requires injectivity. The supplied recursion alone
   is not a constructed colimit. Use Mathlib's actual directed quotient and
   prove seed/Casimir/support transport there, including a native universal
   existence-and-uniqueness theorem. Actual star-ring bonding maps also
   transport reflection, forward corners and Gram expressions through the
   constructed star on the quotient. No analytic norm, spectrum, completion,
   transfer semigroup, or quantitative uniform gap is inferred from this.
4. Real Gram geometry: prove positive semidefiniteness, exact common kernel,
   and positive definiteness iff that kernel is trivial. A dense noncommuting
   real 3-by-3 example has nonzero idempotent Gram support and a nonzero common
   kernel. Thus nonzero coupling does not imply positive definiteness on the
   whole ambient space. This does not deny a positive lower bound on the
   normalized support in the reflexive example.

## Causal prerequisite partial order

The following is an authored prerequisite DAG, not a claim of extracted AST
or theorem-DAG evidence. Its reflexive-transitive closure is the intended
partial order; branches are incomparable unless linked below.

```
existing Peirce decomposition + idempotence
  ├─ reflection weights and square-zero corners
  └─ self-adjointness
       └─ star anti-involution / reflected corner
            ├─ negative anticommutator = Gram sum
            │    └─ real Gram positivity and common-kernel criterion
            └─ alternative star pairing = 0

existing square-zero + reflexivity seed contract
  ├─ support idempotence / Casimir / completed involution
  └─ nonzero seed
       └─ native IsSl2Triple and genuine noncommutativity

native directed ring system + quotient inclusions
  ├─ polynomial seed / support / Casimir transport
  ├─ compatible target homomorphisms → unique universal lift
  └─ injective transition maps
       └─ injective quotient inclusions
            └─ nonzero seed/support and native Cartan triple survive

real Gram criterion + explicit dense real seed pair
  └─ positive-semidefinite but non-positive-definite noncommuting witness
```

No edge identifies finite algebra with a spacetime theory, an analytic gap,
a root-lattice classification, or a continuum reconstruction.

## Verification procedure and status at authoring

Source scripts are complete and contain no proof placeholders. The authoring
runtime has no Lean/Lake binary, so compilation is **pending**, not asserted.
The dedicated workflow uses the repository's unchanged exact Lean/Mathlib
pins, closure resolver and native axiom-audit generator. It
copies exact source bytes, compiles imports sequentially under the shared
build lock, then audits native declarations (including generated/private
ones) against `propext`, `Classical.choice`, and `Quot.sound` only. New modules
are checked with warnings as errors; existing dependency warnings are recorded
without modifying those owners. Independent branches report their errors
together; descendants of a failed import are blocked. Logs and
source hashes are retained. This is not a full root-package Lake build.

Reproduce in a checkout with a matching pinned Mathlib checkout:

```sh
python3 tools/quality/check_peirce_cartan_colimit.py \
  --mathlib-root /path/to/exact-pinned-mathlib --output /path/to/verification
```

Inspect `verification/status.json`, the individual compilation logs, and
`verification/audit.log` before calling the new declarations kernel-verified.

# Real Peirce modes in the existing tensor colimit

## Intake and intent

The exact uploaded stream is preserved in `stream.txt`; `provenance.json`
binds it to the input and to the current repository base. The earlier committed
`Two-Sheeted-Yang-Mills-Inductive-Colimit.md` is the same stream plus one final
newline. Its claims of verification are source material, not acceptance evidence.

The requested construction is real and noncommutative throughout. Polynomial
identities may be stated over an arbitrary associative ring/algebra. All
concrete stages and the concrete limit use real matrix algebras. No
complexification, scalar/diagonal replacement, spectral normalization, or
additional reflexivity assumption is permitted.

## Exact finite claim

Let `p` be an idempotent in an associative algebra, with
`u ∈ Core.PeirceDecomposition.peirce10 p` and
`v ∈ Core.PeirceDecomposition.peirce01 p`. Write, as mathematical notation only,
`E = u+v`, `J = u-v`, `K = u*v+v*u`, `C = ⁅u,v⁆`, and
`s = Core.PeirceGrading.reflection p`.

The native endomorphisms `-(LieAlgebra.ad R A E ^ 2)` and
`LieAlgebra.ad R A J ^ 2` have respective values:

| Input | Negative square at E | Square at J |
|---|---|---|
| K | 0 | 0 |
| E | 0 | `-(4 • (K*E))` |
| J | `-(4 • (K*J))` | 0 |
| C | `-(4 • (K*C))` | `-(4 • (K*C))` |
| s | `-(4 • (K*s))` | `-(4 • (K*s))` |

Their sum is twice the existing native `Core.LieJordanGenerators.symmetricGenerator`.
The coefficient K remains an operator, not a scalar eigenvalue.

## Existing owners and consumed statements

- `Core.PeirceDecomposition` owns the four Peirce components and corner sets.
- `Core.PeirceGrading` owns `reflection`, its square, nilpotence of corners,
  and even/odd reflection laws.
- `Core.PeirceCoupledCorners.coupled_square`: `(u+v)^2 = u*v+v*u`.
- `Core.PeirceQuadraticFrame.difference_square`: `(u-v)^2 = -(u*v+v*u)`.
- `Core.PeirceQuadraticFrame.sum_difference_anticommute` and its bracket
  anticommutation/centralizer lemmas provide the squared-adjoint modes.
- `Core.PeirceCoupledCorners.star_component10` and `star_mem_peirce01`
  exchange the corners for a self-adjoint idempotent; the seed need not be
  self-adjoint.
- `Clifford.Cl11TensorTower` owns the full real stages and actual
  `stageEmbed`, the map `X ↦ X ⊗ I₂`, with `matStageEmbed_injective` and
  `stageEmbed_star`.
- `Clifford.Cl11TensorTowerLimit` owns `Limit`, `ofStage`, its star and real
  algebra structures. `Limit` unfolds to the native root `DirectLimit` quotient.
- `Algebra.DirectLimitSuperClosureLemmas` owns the directed system, canonical
  inclusions, their injectivity and the universal ring lift.
- `Clifford.TowerMatrix.idx_card_pow_two` proves the stage index cardinality.

## Exact colimit claim

Expose the existing stage inclusions and universal ring map as native
`StarAlgHom ℝ`. Prove that a family of real unital star-algebra homomorphisms
from the actual stages admits a unique factorization through the existing
Limit exactly when it respects the actual tensor bonding maps.

Transport the specified Peirce operations, star/reflection Gram expression,
and double-commutator endomorphism actions along the actual inclusions.
Use faithfulness to reflect equality and preserve noncommutation. Prove
`¬ FiniteDimensional ℝ Limit` from injective linear maps of full matrix stages
and their unbounded dimensions. This establishes an infinite-dimensional
algebraic target, without constructing a completion.

## Proof prerequisites

1. Associative algebra and idempotent support give opposite-corner products,
   squares and parity (existing owners).
2. These quadratic identities and native `LieAlgebra.ad` give the exact
   double-commutator mode table.
3. The existing real matrix tower and native quotient give faithful
   canonical inclusions and universal ring descent.
4. The existing star/scalar structures strengthen descent to native real
   star-algebra descent; this branch does not depend on the mode table.
5. Naturality and the actual inclusions transport the finite mode/reflection
   statements into the limit.
6. Faithful linear inclusions and stage cardinalities prove infinite dimension.
7. Full real matrix witnesses and faithful inclusions exhibit noncommutation
   in the limit.

This is a proof-prerequisite DAG. It does not claim to be a generated
declaration-level dependency graph or a new physical causal structure.

## Adjacent claims outside the contract

Odd conjugation parity is an algebraic grading statement. A Gram decomposition
in a star ring is not a theorem about an ordered representation or an
Osterwalder–Schrader functional. The weighted mode equations do not establish
a scalar spectral gap, a uniform coercivity estimate, an analytic completion,
or a four-dimensional quantum Yang–Mills theory. The attachment's claim that
all 52 prior archetypes lift is not part of this finite, enumerated contract.

## Verification requirements

Compile the exact source closure at the repository pins; use the shared build
lock and inspect concurrent processes. Run the native exhaustive declaration
audit against `propext`, `Classical.choice`, and `Quot.sound`, and a native
isolated Lake build. Preserve source hashes and logs. Independent semantic
review and acceptance must distinguish kernel validity from the intake's
interpretation. Existing dependency pins and root package configuration stay
unchanged.

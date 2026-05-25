# Repository Boundary Policy: Conditional Interfaces vs Global Realizations

Status: active policy

Safe statement:

The repository currently contains conditional interfaces and local algebraic
seeds, not global geometric realizations.

## Repository boundary declaration

These are type-theoretic firewalls, not optional caveats.

## Hard boundaries

1) Souriau global realization boundary
- No concrete Souriau coadjoint-orbit model is currently proved for `G₂(2)`,
  `G2*`, or `Spin(5,5)` with explicit `Ad`, `Ad*`, Souriau cocycle, and
  Fenchel/Legendre map in one closed realization.
- `Souriau` files remain abstract dual-pair/cocycle interfaces until those data
  are constructed.

2) Split-current source-construction boundary
- No proved source-side theorem currently constructs affine current witness data
  (`J`, truncation, commutator law) directly from split completion alone.
- Current/Sugawara bridge files are conditional adapters:
  witness-in (`CurrentHeisenbergRep` / split witness), Sugawara-out.

3) Zorn algebra boundary
- No theorem states split octonions are ordinary associative `2×2` block
  matrices.
- Zorn lane uses custom (generally nonassociative) vector-matrix product.
- Determinant theorems are composition-algebra theorems, not ordinary matrix
  Binet–Cauchy multiplicativity claims.

4) Twistor identification boundary
- No theorem states “twistor space equals split octonions” definitionally.
- Target theorem direction is structural: suitable quantized twistor algebra
  carries split-octonion / `G2*` structure under explicit hypotheses.

## Dependency posture

Souriau layer:
- abstract dual pair
- abstract coadjoint action
- abstract Souriau 1-cocycle
- Bregman/Fenchel interfaces
- debt: concrete `G₂(2)` / `Spin(5,5)` realizations

Split-current layer:
- zero-mode seed / boundary data
- constructive current theorem surface
- conditional witness bridge into Sugawara
- debt: split source => `J`, `trunc`, `comm`

Zorn/split-octonion layer:
- Zorn cells / determinant / projective null shell
- composition identity lane
- no associative-matrix API claims

Twistor layer:
- projective twistor null geometry
- incidence/Hermitian surface
- debt: quantized twistor CCR carries `Os` and `G2*`

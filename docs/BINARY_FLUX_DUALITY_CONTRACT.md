# Binary electric–magnetic flux: theorem contract

## Source and intended scope

This intake concerns G. 't Hooft, *A property of electric and magnetic flux in
non-Abelian gauge theories*, Nuclear Physics B153 (1979), 141–160,
[doi:10.1016/0550-3213(79)90595-9](https://doi.org/10.1016/0550-3213(79)90595-9).
The supplied 20-page scan has SHA-256
`136a55f8b51dff925a540084f5f9c6944e19e22d3997239ea52d71faad395ffe`.
Printed pages 148–149 are PDF pages 8–9. The source equations were checked
against the page images, rather than relying on OCR alone.

Base revision: `586c14bc9fb94eb09b56f7dc850d9d5297269f91`.
The intended contribution is finite real algebra for **N = 2**. The
three-component electric projector has normalization **1/8**. The transverse
duality acts on sixteen electric–magnetic pairs with normalization **1/4**.
These are different operations.

For the transverse formula, `W` denotes the longitudinal Fourier projection
`(1/2) Σ k₃, χ(e₃,k₃) W_full((k,k₃),(m,m₃))`, at fixed `e₃,m₃`.
It does not mean fixing `k₃`. The rotation in (6.2) leaves `k₃,m₃` fixed,
so this projected table inherits the transpose covariance. The formalization
will also prove this inheritance.

## Causal theorem chain

| Source claim | Native carrier and missing implication | Classification |
|---|---|---|
| (4.4), (5.2): average a flux-group representation against a character | `Multiplicative (ι → ZMod 2) →* A`, with `A` an arbitrary real algebra; construct the normalized representation transform | Finite algebra, theorem target |
| Sector selection | Derive projector products, completeness, and the character eigenrelation from the representation law and Walsh orthogonality | Finite algebra, theorem target |
| (4.8)–(4.10): charge transport | Derive ordered projector transport from an explicitly supplied charge covariance relation | Conditional finite algebra, theorem target |
| (5.3): linear measurement of a projector | Push the constructed finite sum through a real linear functional, keeping the order of multiplication by a supplied operator | Finite algebra, theorem target |
| (5.4): electric forward transform and inverse | After longitudinal Fourier projection, use the transverse real Walsh matrix `H`, with `H² = 4 I`; forward transform `H W / 4`, inverse `H Z` | Finite algebra, theorem target |
| (6.2) implies (6.3) | Derive `Z = H Z'ᵀ H / 4` from the explicit covariance hypothesis `W = W'ᵀ` | Conditional finite algebra, theorem target |
| Repeating the transverse transform | Prove the actual matrix map `D(X) = H Xᵀ H / 4` is an involution | Finite algebra, theorem target |
| Euclidean functional integral and covariance | Construct the gauge theory and prove the covariance input | Open physical/analytic debt |
| §7: asymptotic light/heavy sectors and confinement | Supply the mass, spatial symmetry, limit, and positivity arguments in their physical setting | Open physical/analytic debt |
| (7.4): additive electric/magnetic free energy | The paper explicitly assumes this asymptotic factorization; finite Fourier algebra does not prove it | Model assumption, not a theorem target |

The binary characters are real signs. For N > 2, replacing a complex phase
by its cosine does not preserve individual character sectors. A general-N
real realization requires additional compatible real phase operators and is
outside this change.

## Existing owners and reuse decision

The bounded owner search covered actual definitions, theorem statements,
proofs, imports, and consumers in `lean/` and `src/`.

- `LLM/WalshCharacterGeometry.lean` owns native real `AddChar`s on
  `ι → ZMod 2`, character symmetry and orthogonality, and the actual Walsh
  matrix orthogonality law. Reuse these results directly.
- `Algebra/FiniteGroupFourier.lean` owns the representation transform via
  `MonoidAlgebra.lift`, its finite-sum evaluation, and its ordered convolution
  product. Reuse it for operator-valued projectors.
- `Algebra/FiniteGroupCharacterProjection.lean` already proves normalized
  projection onto a supplied unit-valued character using Mathlib's invariant
  submodule and averaging APIs. The new binary owner supplies the complete
  explicit character family and its joint multiplication/completeness laws.
- `Canonical/V4GroupFourierTransform.lean` and
  `Canonical/V4CharacterGibbsPoUBridge.lean` own the four-character regular
  function representation. They do not provide the arbitrary real-algebra
  eight-sector construction.
- `Canonical/FiniteHeisenbergGroup.lean` owns the finite alternating group
  commutator. `Weyl/OperatorBraiding.lean` owns genuine noncommutative
  clock/shift holonomy. Neither construction is duplicated here.
- `Canonical/CyclotomicProjectorReadout.lean` stores several spectral laws
  as supplied fields; those fields are not used to claim their construction.

The ambient operator algebra remains potentially noncommutative. The image
of the abelian flux subgroup commutes by its representation law. Individual
sector projectors may be zero; nonzero occupation of every sector is not
implied by that law.

## Interpretation boundaries

The conditional covariance theorem must derive duality from the twisted-table
transpose relation and Fourier inversion. It must not accept the desired
duality equation as a structure field. A linear functional is not silently
identified with a trace-class Gibbs trace.

Finite duality alone cannot classify physical phases. For example, the binary
set `{(e₁,e₂;m₁,m₂) | e₂ = 0, m₁ = 0}` mixes electric and magnetic directions
while satisfying finite symplectic self-duality and nonnegativity of both the
table and its inverse electric transform. Its zeros do not demonstrate strict
finite-volume positivity.
The paper's physical classification also uses spatial and asymptotic
assumptions. This observation is a scope guard, not a new confinement result.

The signed Fourier transform here is distinct from the positive diagonal
Sinkhorn scaling in PR #412. No equivalence between those algorithms or their
physical applications is asserted, and this change does not depend on that
unmerged PR.

## Validation and acceptance plan

Keep the pinned Lean 4.34.1 and Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Compile the new owners and their
actual dependency closure under the maintained shared build lock. Run the
repository's strict source checks and a declaration-level axiom audit,
including generated declarations. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted foundational dependencies.

Generation, independent source audit, and acceptance QA use separate agents.
The final validation record will distinguish successful focused verification
from any unresolved root-package build or publication gate.

Final mathematical status: **finite targets kernel-verified; physical
covariance/charge premises remain explicit; root integration is blocked**.
The two new owners passed fresh compilation and all-declaration axiom auditing.
See [the validation record](BINARY_FLUX_DUALITY_VALIDATION.md) for exact hashes,
commands, independent review, heuristic warnings, and the root-package failure.

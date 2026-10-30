# AI Studio operator arithmetic: claim map and formalization status

This note distills the arithmetic/resolvent/duality fragment of the AI Studio
histories into typed mathematical claims and maps them to repository owners.
Prompt text and extracted Lean fences are intake evidence only. The Lean owners
below are the source of theorem truth.

## Three different meanings of “delta”

Do not identify these constructions:

1. **Polynomial defect:** for an element `x` of an associative ring,
   `idempotencyDefect x = x * x - x`. It is generally neither central nor a
   distribution. The owner proves complement symmetry, functoriality,
   conjugation covariance, and
   `δ(-x) * δ(x) = δ(x²)` in
   [`IdempotentGraphGrassmannian.lean`](../lean/InfoGeometry/Core/IdempotentGraphGrassmannian.lean).
2. **Dirichlet-convolution unit:** `ArithmeticFunction 1` is the identity for
   Dirichlet convolution. Its value is `1` at the natural number `1` and `0`
   elsewhere. It is a discrete arithmetic identity, not the polynomial defect
   and not a distribution. See
   [`MatrixDirichletInversion.lean`](../lean/InfoGeometry/Arithmetic/MatrixDirichletInversion.lean).
3. **Resolvent kernel delta:** the entries of the identity matrix are
   `if i = j then 1 else 0`; the matrix resolvent equation makes the finite
   Green kernel reproduce this Kronecker delta. See
   [`CharacteristicResolvent.lean`](../lean/InfoGeometry/OperatorAlgebra/CharacteristicResolvent.lean).

The common word “delta” does not supply a map between these objects.

## Dependency-ordered archetypes

```text
Peirce idempotent P² = P
  └─ PeirceSpine/Tetraktys: N₊, N₋; Φ² = V and J² = -V
       ├─ PeirceSpine/TransferDefect: T = P + Φ; δ(T) = V; V-weighted recurrence
       ├─ Core/IdempotentGraphGrassmannian + PeirceSpine/DefectTower (A₃₉):
       │    δ iteration, dyadic telescoping, orthogonal Q₊/Q₋ defect splitting
       ├─ A₄₀: defect remainders from TransferDefect and Core defect calculus
       ├─ PeirceSpine/PrimalDual (A₄₂): graph chord products identify with Q₊, Q₋
       ├─ PeirceSpine/ChiralEulerFactors (A₄₃): ordered products give 1 ± V, 1 ± Σ
       │    └─ A₄₄: even-grade and four-supercharge factorizations
       └─ OperatorDirichlet/Resolvent (A₄₁): general cyclotomic evaluation/factorization
            └─ OperatorDirichlet/SpineResolvent: Peirce-generator specializations
                 └─ MatrixPeirceResolvent: det(z²I ∓ V) criteria for Φ/J resolvents;
                      chiral factor determinants imply both resolvents at z=1

ArithmeticFunction convolution
  └─ ζ and μ are two-sided convolution inverses
       ├─ matrix-valued coefficient inversion (factor order retained)
       └─ log and von Mangoldt convolution identities

PeirceSpine/ChiralEulerFactors (A₄₃)
  ├─ PeirceSpine/Supercharge (A₄₄): ordered four-supercharge/cycle identity
  └─ MatrixDirichletInversion.impulseRingHom: matrices embed multiplicatively
       └─ OperatorDirichlet/MatrixChiralConvolution: A₄₃ factors and the
          A₄₄ four-supercharge identity transported to matrix convolution
       └─ ζ * impulse(A) has coefficient A at every positive index

Finite matrix A and spectral parameter z
  └─ charpoly nonvanishing gives inverse of zI - A
       ├─ adjugate formula and two-sided resolvent identities
       ├─ ordered resolvent perturbation identity
       └─ finite Green-kernel/Kronecker-delta identity

Convex potential and dual covector
  └─ Fenchel/Legendre support supremum and contact/equality laws
```

The displayed branches are ordered internally by their actual hypotheses and
imports. No edge between the arithmetic-convolution branch, the matrix
resolvent branch, and the Fenchel branch is asserted without a concrete map
and a compatibility theorem.

`Algebra/PeirceOmegaTransfer.lean` and
`Algebra/SteinbergBraidDefectSpine.lean` are also present and build, but the
canonical modular Peirce owner is `OperatorAlgebra/PeirceSpine/`. The transfer
owner explicitly says an identification with the golden-mean shift adjacency
operator needs a separate carrier map. Keep future claims on the modular owner
and avoid growing two competing definitions of the same operator spine.

## Owner map and proved scope

| Archetype | Repository owner | Formal scope |
|---|---|---|
| Associative-ring defect calculus | `Core/IdempotentGraphGrassmannian.lean` | Polynomial identities for `x*x-x`; no centrality assumption. The cubic identity is `x³ - x² = x * δ(x)`. The variant `x³ - x² - x = x * δ(x)` is false except at `x=0`. |
| A₃₉ defect iteration and Peirce sheets | `Core/IdempotentGraphGrassmannian.lean`, `OperatorAlgebra/PeirceSpine/DefectTower.lean` | The quartic expansion of `δ(δ(x))`, its vanishing when `δ(x)=1`, dyadic telescoping, and additive defect iteration for orthogonal operators; specialized to the two mutually annihilating Peirce cycles. The cycles need not themselves be idempotents. |
| Peirce algebra and transfer | `OperatorAlgebra/PeirceSpine/{Tetraktys,TransferDefect}.lean` | In the existing noncommutative Peirce owner, `T=P+Φ` has defect `V`; `T²=T+V`; complementary Vieta products and the `V`-weighted power recurrence. The scalar seed `T²=T+1` needs the extra hypothesis `V=1`. |
| A₄₀ Euler/Bergman defect remainders | `OperatorAlgebra/PeirceSpine/TransferDefect.lean`, `Core/IdempotentGraphGrassmannian.lean` | Exact finite polynomial remainders, including the corrected chiral Mangoldt product. Does not assert an analytic zeta function or logarithmic derivative. |
| A₄₁ cyclotomic operator identities and Peirce resolvents | `OperatorAlgebra/OperatorDirichlet/{Resolvent,SpineResolvent}.lean` | Nilpotent resolvents, Peirce-generator resolvents under explicit unit hypotheses, and general operator cyclotomic factorization. The broader aggregator `OperatorAlgebra/OperatorDirichlet.lean` also imports convolution and matrix-Legendre owners. |
| A₄₂ graph chord potentials | `OperatorAlgebra/PeirceSpine/PrimalDual.lean` | The ordered products of the two graph-transformed idempotents are `Q₊` and `Q₋`; their sum and difference are `V` and `Σ`. |
| A₄₃ Peirce partition and chiral factors | `OperatorAlgebra/PeirceSpine/ChiralEulerFactors.lean` | Ordered products of the mutually annihilating corner cycles give `1 ± V` and `1 ± Σ`; the factor names remain finite ring expressions. |
| A₄₄ supercharge factorization | `OperatorAlgebra/PeirceSpine/Supercharge.lean`, `OperatorAlgebra/PeirceSpine/ChiralEulerFactors.lean` | Exact ordered mixed-product expansions, even-grade extraction, and a direct ordered equality of the four-supercharge and four-cycle products, both equal to `1 - V²`. |
| Chiral factors as resolvent characteristic units | `OperatorAlgebra/OperatorDirichlet/SpineResolvent.lean` | If the ordered factors `(1-Q₊)(1-Q₋)` or `(1+Q₊)(1+Q₋)` are units, the generic resolvent theorem gives two-sided inverses for `1-Φ` or `1-J`. This is conditional on an actual unit and preserves order; it asserts no unconditional invertibility. |
| Finite matrix Peirce resolvent bridge | `OperatorAlgebra/OperatorDirichlet/MatrixPeirceResolvent.lean` | For full complex matrices and arbitrary spectral parameter `z`, named determinant factorizations express `det(zI−Φ)det(zI+Φ)=det(z²I−V)` and `det(zI−J)det(zI+J)=det(z²I+V)`. Nonzero mass determinants yield the respective two-sided resolvents; the `z=1` results are corollaries. A named chiral determinant product theorem establishes `det(1−Σ)det(1+Σ)=det(1−V)det(1+V)`, so nonzero chiral factors jointly imply both resolvents at `1`. Proofs use ordered quadratic factorizations and characteristic determinants; no diagonalization is used. |
| Matrix-valued arithmetic inversion | `Arithmetic/MatrixDirichletInversion.lean` | Left/right Möbius inversion for arbitrary full-matrix coefficients; the injective ring hom from matrices to impulses at convolution index 1; noncommuting matrix impulses; zeta/log/von-Mangoldt action. This is a genuine matrix-valued theorem, with multiplication order preserved. |
| Zeta action on matrix impulses | `Arithmetic/MatrixDirichletInversion.lean` | The divisor-sum formula gives `(ζ * impulse A)(k) = A` for every positive `k`; this is a coefficientwise arithmetic-function identity, not an analytic Dirichlet series. |
| A₄₃–A₄₄ matrix-convolution transport | `OperatorAlgebra/OperatorDirichlet/MatrixChiralConvolution.lean` | The injective point-mass ring hom at arithmetic index 1 transports all four finite Peirce chiral-factor identities and the ordered four-supercharge/cycle identity to matrix-valued convolution. This does not assert an analytic Euler product. |
| Characteristic polynomial and resolvent | `OperatorAlgebra/CharacteristicResolvent.lean` | For finite matrices, `charpoly.eval z ≠ 0` gives a two-sided inverse of `zI-A`; the inverse has the adjugate numerator, and the resolvent identity preserves order. |
| Convex duality | `Geometry/LegendreDuality.lean`, `OperatorAlgebra/OperatorDirichlet/MatrixLegendre.lean` | Fenchel support inequalities/contact laws and the specific quadratic operator Legendre conjugacy owned by `MatrixLegendre`. This is not an automatic transform of a Dirichlet partition function. |
| Peirce chiral-factor identities | `OperatorAlgebra/PeirceSpine/ChiralEulerFactors.lean` | Ordered polynomial products from the two orthogonal Peirce cycles, their even-grade supercharge factorizations, and the four-factor identity `1 - V²`. These are finite ring identities; analytic zeta/L-functions and Galois extensions are not claimed. |

## Corrections to the brainstorm

- The total graded derivation satisfies `dΦ²(X)=[V,X]`. The new
  `PeirceSpine/CentralizerDifferential.lean` proves that its square vanishes
  exactly on elements commuting with V, proves that this centralizer is
  preserved, and constructs the restricted map with square zero. This is
  a square-zero map on the invariant subtype; a bundled graded cochain
  cohomology is now explicitly constructed in `CentralizerCohomology` as the
  additive kernel/range quotient; no manifold interpretation is asserted.
- Updated transcript turn 35 claims in prose that `d̄Φ(1-Σ)=0`, while
  its Lean packet only states `d̄Φ(Σ)=0`. The new owner
  `PeirceSpine/ChiralDifferentials.lean` proves `dΦ(1-V)=0`,
  `d̄Φ(Σ)=0`, and the exact residual `d̄Φ(1-Σ)=2 • Φ`.
  Coclosure of the factor therefore holds exactly when `2 • Φ=0`.
- The graded Laplacian is `Δ(X)=2 • (V*X+X*V)`, not `2 • (V*X)`.
  `PeirceSpine/Orientation.lean` proves the corrected formula and the two
  reconstruction laws `Δ(X)+2 • [V,X]=4 • (V*X)` and
  `Δ(X)-2 • [V,X]=4 • (X*V)`. Thus the proposed A₃₂ generation formulas
  cannot be justified by substituting the transcript's Laplacian formula.
  These reconstruction laws require neither division by 2 nor centrality of V.
  `PeirceSpine/LaplacianHomogenization.lean` now proves the corrected A₃₂
  generation identities for all four channels. With `K=Δ+2 • connV`, the
  V-channel satisfies `4 • hProjV(X)=2 • K(K(X))+K(MΦ(X))+K(MJ(X))+4 • MΣ(X)`;
  the other three are the corresponding signed differences. The statements
  retain the factor 4, which cannot be cancelled in an arbitrary ring.
- The identity `δ(-X)δ(X)=δ(X²)` is valid because both factors are
  polynomials in the same element `X`. It does not imply a Galois extension.
- A matrix sandwich such as `X ↦ V * (Φ * X * Φ)` is generally a scaled linear
  operator, not a ring automorphism. The four sandwiches therefore do not by
  themselves constitute a Klein-four Galois group, and their Fourier sums are
  not automatically a Galois trace or Hilbert-90 resolvents.
- `ℤ[V]` need not be a field; it may have a nontrivial kernel in the polynomial
  evaluation map. A field extension or a finite Galois extension requires
  additional hypotheses and a proved carrier/fixed-ring construction.
- Matrix-valued Möbius inversion is already formalized, but it does not by
  itself establish a noncommutative Euler product, a product formula for
  partition functions, or a relation to the Mandelbrot set/Fourier transform.
  The stream itself says its “Mandelbrot–Fourier” and “Riemann zeta product”
  phrases lack a pinned operator statement.
- “Resolvent ringing” can be made precise through the resolvent identity and
  the characteristic polynomial/adjugate formula. A trace-log derivative or
  spectral-density formula is a separate claim and must be stated with its
  domain and regularity hypotheses before it is formalized.
- The chiral Euler-factor identities in `PeirceSpine/ChiralEulerFactors.lean`
  are formal factorizations in the Peirce corners. Their labels do not assert
  graph-prime, analytic Euler-product, or Dirichlet-L-function structure.
- The matrix impulse bridge is now an injective ring hom into matrix-valued
  arithmetic functions supported at index `1`; it transports the A₄₃
  factorizations and A₄₄ four-supercharge identity. This finite support
  embedding does not define graph cycles or analytic Euler products.
- The chiral-factor resolvent corollaries require a supplied unit witness whose
  underlying value is exactly the ordered factor. The finite factorization
  alone does not prove that this element is invertible.
- The second defect iterate expands as `δ(δ(x)) = x⁴ - 2x³ + x`. The proposed
  identity `(1-x)(1+x+x²)-1 = -(1+x)δ(x)` is false in general; the exact
  left side is `-x³`, and its defect rewrite includes the additional `-x`.
- The proposed A₄₃ chiral Mangoldt readout
  `Σ - V² - V*δ(V)` simplifies to `Σ - V³` and is not the stated product.
  The Peirce owner proves the ordered identity
  `(1-Σ)*(Σ + V*Σ) = (1+V)*(Σ - V²)` in
  `PeirceSpine/TransferDefect.lean`; its expansion is
  `Σ + V*Σ - V² - V³`, differing from the proposed expression by `V*Σ - V²`.
- In the A₄₄ mixed supercharge products, the odd residuals lie in the `N₋`
  corner for all four displayed orders. In particular,
  `(1-J)*(1+Φ) = 1-Σ+2*N₋` and
  `(1+Φ)*(1-J) = 1+Σ+2*N₋`; replacing those residuals by `2*N₊` is a
  sign/corner error. The even-grade projections in
  `PeirceSpine/ChiralEulerFactors.lean` and exact mixed-product expansions in
  `PeirceSpine/Supercharge.lean` are the supported identities.

## Source numbering collisions

In the refreshed 35-turn `1t9Q3cbWphRcmuigvp9LZomzS7Q8Pclxe` export,
archetype number alone does not identify a mathematical obligation:

| Source turns | Label | Mathematical obligation |
|---|---|---|
| 24 | A₂₉ | Graded Laplacian and corner products |
| 26, 28 | A₂₉ | Graded derivations and their squares |
| 24 | A₃₀ | Proposed cochain complex |
| 26, 28 | A₃₀ | Graded Laplacian and corner products |
| 26, 28 | A₃₁ | Proposed cochain complex |
| 28 | A₃₂ | Homogenized-channel generation (corrected owner: `LaplacianHomogenization`) |
| 28 | A₃₅ | Grading eigenspaces and complementary-idempotent reversal |
| 29, 31 | A₃₅ | Idempotency-defect calculus |
| 28 | A₃₆ | Left/right actions and their squares (`LeftRightActions`, kernel checked) |
| 29, 31 | A₃₆ | Golden-equation level set and unit pair |

The occurrence list was read from theorem declarations in the extracted code
fences. It records source identity, not verification coverage. Future coverage
entries must include the source turn and mathematical statement; matching only
an archetype label can silently conflate different theorems.

## Next theorem-sized gaps

The additive centralizer differential, its square-zero composition, the
kernel/range quotient in `CentralizerCohomology.lean`, the Phi/J action,
square and anticommutation laws in `LeftRightActions.lean`, and the
complement-exchange laws in `ComplementSymmetry.lean` passed locked Lake
builds. These are ring-level constructions, with no assertion of a manifold
cohomology or Galois extension.

The subsequently pasted consolidated A₁–A₄₄ packet is a separate source
version. Its numbering places defect calculus at A₃₇, the seed equation at
A₃₈, and the sandwich/resolvent packet at A₄₀. It retains the false cubic
identity at A₃₈, the missing right-multiplication terms at A₃₀/A₃₂/A₃₄,
and the incorrect geometric-series remainder at A₄₃:
`(1-V)*(1+V+V²)-1 = -V³`, whereas `-(1+V)*δ(V) = V-V³`.
The corrected owners remain authoritative; this packet is not a verified
replacement. Its A₄₀ theorem does not state or prove a Galois group isomorphism.

1. Extend the index-1 impulse model to a specified arithmetic-indexed
   matrix-valued operator sequence whose coefficients encode the chiral
   factors; prove the convolution law for those coefficients. The current
   zeta action on an impulse is constant on positive indices and does not
   encode a graph or operator Euler product.
2. If the target is a resolvent/partition identity, formulate it using the
   existing `resolvent`, `charpoly`, and arithmetic-function owners; retain
   the noncommuting factor order and all invertibility hypotheses.
3. If the target is a Legendre relation, use the existing operator
   `MatrixLegendre` carrier and prove the proposed partition potential is its
   input. Do not infer convex duality from an informal “inverse” analogy.
4. For any proposed operator Galois claim, first define the algebra/carrier,
   actual algebra automorphisms, their action and fixed subring, then prove
   the group law and trace/resolvent statements. The scaled sandwich formulas
   alone do not meet that contract.

## Corrected mixed graded compositions (consolidated A₃₀)

`PeirceSpine/MixedDifferentials.lean` supplies seven named lemmas, checked
in the arbitrary associative ring carrier:

- The barred Phi and J squares are respectively `ad_V` and `-ad_V`.
- The J/barred-J anticommutator is `-2 • (V*X + X*V)`.
- Both crossed Phi/J barred anticommutators vanish, rather than yielding
  the proposed `±2 • (Σ*X)`.
- The ordered corner sums are `2 • (Q₊*X + X*Q₋)` and
  `2 • (Q₋*X + X*Q₊)`. Omitting the right terms changes the theorem.

Dependency: `Supercharge → Orientation → MixedDifferentials`. No Galois,
analytic zeta, or manifold-cohomology interpretation is inferred from these
endomorphism identities.

## Generator evaluations (consolidated A₃₁)

`PeirceSpine/GeneratorDifferentials.lean` proves 19 named evaluation lemmas.
Together with `ChiralDifferentials.superDerivPhiBar_genSig`, they cover all
18 displayed A₃₁ conjuncts and add the individual vanishing identities
`dPhi(J)=0` and `dJ(Phi)=0`. The statements retain arbitrary ring
characteristic and arbitrary off-diagonal inputs A,C. In particular,
`dPhi(S)=-2J`, `dJ(S)=-2Phi`, `dPhi(Phi)=2V`, and `dJ(J)=-2V`.
The source's three-degree de Rham interpretation is not supplied by an
evaluation table: the independently constructed square-zero map lives on
the V-centralizer, where its kernel/range quotient is defined.

The current Orientation owner also characterizes the erroneous left-only
Laplacian formula: at X it holds iff `2 • (X*V)=0`; for all X it holds iff
`2 • V=0`. This retains the characteristic-two case without cancellation.

## All finite defect iterates

The source claim that *every* iterate splits across the two Peirce sheets is
now expressed with `Function.iterate`, beyond the first two expanded cases.
`Core/IdempotentDefectIteration.lean` proves preservation of one-sided
annihilation, additive splitting of mutually orthogonal inputs for every
natural iterate, and transport of the finite orbit by any ring homomorphism.
`PeirceSpine/DefectTower.lean` specializes these results to Q₊ and Q₋,
proving both the split of the orbit of V and persistent two-sided
orthogonality of the iterated cycles. These are finite algebraic iteration
laws, not claims about a Mandelbrot set, analytic convergence, or an
infinite categorical boundary.

Dependency: `IdempotentGraphGrassmannian → IdempotentDefectIteration`,
then together with `Supercharge → DefectTower`.

## Complementary transfer-power recurrence

`PeirceSpine/TransferMoments.lean` proves that the complement `1-T` satisfies
the same quadratic relation and all-index power recurrence as `T=P+Phi`.
For `L(n)=T^n+(1-T)^n`, the proved recurrence is
`L(n+2)=L(n+1)+V*L(n)`, with `L(0)=1+1`, `L(1)=1`,
`L(2)=1+2 • V`, and `L(3)=1+3 • V`.
The general quadratic-power helper in `TransferDefect` is now public and
reused instead of reproving the power induction. Dependency:
`TransferDefect → TransferMoments`. These power sums are not asserted to
be the scalar collision statistics of the external Omega project, nor does
a second-order recurrence prove the transcript's advertised third-order
collision recurrence.

## Parity orbit sums and ordered products

`PeirceSpine/ParityProducts.lean` reuses the existing involutive ring action
from `Supercharge`. It proves that `X+sigma(X)` is fixed and that
`sigma(X*sigma(X)) = sigma(X)*X`. Thus the ordered product is fixed exactly
when `Commute X (sigma(X))`. This is the precise restriction behind the
source's proposed Galois norm: no universal fixedness or multiplicativity of
that product is asserted. The division-free orbit sum/difference formulas
are `X+sigma(X)=2 • evenGrade P X` and
`X-sigma(X)=2 • oddGrade P X`; these polynomial identities do not require
P to be idempotent. Involutivity and the fixedness results do require it.
Dependency: `Supercharge → ParityProducts`.

## Grading perturbations and transfer discriminants (A₄₅–A₅₀)

The extracted algebra is organized into four focused owners:

- `GradingPerturbation`: squares of `S ± Phi` and `S ± J`, ordered
  sandwiches, and first and second commutators (A₄₅–A₄₆).
- `RingHomTransport`: naturality of the polynomial operators under arbitrary
  ring homomorphisms, including composition (the algebraic part of A₄₇–A₄₈).
- `MatrixColimitTransport`: coherence under the bonding maps of the existing
  `Cl11TensorTowerLimit`, and the grading square in its actual limit ring.
- `GradingTransfer`: equality of transfer defect and grading square minus one,
  characteristic-free discriminant completion, and the two coupled
  double-commutator identities (A₄₉–A₅₀).

The causal order is corner multiplication → grading relations → perturbation
identities. Transfer defects join this branch at `GradingTransfer`.
Homomorphism transport is a separate branch; the matrix-limit result also
depends on the existing direct-limit carrier and bonding-map coherence.

No independence or spanning theorem makes the displayed elements an
eigenbasis. The coefficient `4 • (1+V)` acts by left multiplication in the
ambient ring. The sandwich `H*S*H` is not asserted to be conjugation by an
invertible element. At `V=0` it equals `S+2 • Phi`; the unchanged-grading
claim holds exactly when `2 • Phi=0`. Polynomial naturality alone does not
establish cohomology preservation or correctness of content hashes.

## Unit defect level set

`DefectLevelSet.lean` bundles the inverse-pair claim as an actual `Bˣ`:
under `delta(V)=1`, its value is `V+Phi` and its inverse is `V-Phi`.
Both inverse equations reuse `TransferDefect.genPhi_defect_product`.
The same file proves `V^(n+2)=V^(n+1)+V^n` for every natural n and
`delta(delta(V))=0`. The latter two results require only the level-set
equation; they do not require P's idempotence. This formalizes the source's
conditional seed consequences without imposing ambient commutativity.

## Mode coordinates and the eigenbasis claim

`ModeCoordinates.lean` gives a precise reconstruction theorem for the source
pair `D=V*Phi+Sigma`, `E=Phi-Sigma`. Universally,
`D+E=(1+V)*Phi` and `D-V*E=(1+V)*Sigma`. For a unit `u=1+V`,
`modeCoordinateEquiv u : (B × B) ≃+ (B × B)` sends `(Phi,Sigma)` to
`(D,E)` and explicitly inverts the change of coordinates. Its inverse sends
`(d,e)` to `(u⁻¹*(d+e), u⁻¹*(d+e)-e)`.
These are noncommutative operator formulas. The unit hypothesis is sufficient
for this inverse; the file does not claim it is necessary on a smaller
generated module. Neither this coordinate change nor the double-commutator
identities prove independence of `V,D,J,E`. Dependency:
`GradingTransfer → ModeCoordinates`.

## Automorphisms on the unit-square level set

`UnitSquareAction.lean` constructs `phiUnitSquareEquiv : B ≃+* B` under
`P*P=P` and `V=1`, with action `X ↦ Phi*X*Phi`. It proves involutivity
and commutation with `Supercharge.parityConjRingEquiv` on all of B.
The generic helper `squareOneConj` packages conjugation by any square-one
ring element as a ring equivalence. This supplies the two commuting
involutions behind the source's Klein-four claim in a precise conditional
form. No unconditional automorphism status is assigned to the scaled
sandwiches, and no faithfulness or Galois theorem is inferred.
Dependency: `Supercharge → UnitSquareAction`.

`KleinAction.lean` now packages these relations as
`peirceKleinHom : Multiplicative (ZMod 2 × ZMod 2) →* (B ≃+* B)`.
The source group is mathlib's standard Klein-four carrier, and the target
uses its ring-automorphism group structure. Identity and multiplication
preservation are proved. The construction retains `P*P=P` and `V=1`;
injectivity of the action is not claimed. The reusable `kleinHom` helper
constructs the same homomorphism for any pair of commuting involutions in
an arbitrary group. Dependency: `UnitSquareAction → KleinAction`.

## Later A49–A50 packet: graded defect decomposition

This packet reuses the labels of the discriminant packet; its owners are
`GradedDefect.lean` and `GeneratorDefect.lean`, not replacements for
`GradingTransfer.lean`. The former proves parity equivariance, the even/odd
defect decomposition, and the exact square-zero criterion for idempotence
of `P+oddGrade P X`. It also proves the division-free parity-difference
square and the corrected ordered product with the negative commutator term.
The latter contains 14 named generator specializations: the skew
commutators, defect-as-negative-commutator-square identities, second-level
defect product, graded components, and the double-derivation differences.

Two corrections to prose are recorded in the theorems themselves:
`[S,V+Phi]=2 • J` (not its negative), and
`(P+Phi)*sigma(P+Phi)=P-V-J` (not `P-V+J`). No division by two or four
is introduced. Peirce grade projections remain meaningful in characteristic
two, where the involution's sign eigenspaces cannot distinguish the grades.
Neither a Hilbert 90 theorem nor a Galois-extension claim follows from this
packet. Actual dependency: corner relations and parity ring equivalence →
`GradedDefect`; together with generator multiplication → `GeneratorDefect`.

## The additive cocycle statement

`ParityCoboundary.lean` formalizes the actual group variable: for every
ambient operator X, `b_X(g)=X-g(X)` on the ring-automorphism group satisfies
`b_X(gh)=b_X(g)+g(b_X(h))`, and `b_X(1)=0`. For fixed g, the map
`D_g(X)=X-g(X)` is bundled as an additive homomorphism, with twisted
Leibniz law `D_g(XY)=D_g(X)Y+g(X)D_g(Y)`. Its kernel consists exactly
of g-fixed elements. For parity, `D_sigma(X)+sigma(D_sigma(X))=0` and
`D_sigma(X)=2 • oddGrade P X`.
This is an explicit additive coboundary calculation, not a proof of
Hilbert 90, surjectivity onto all trace-zero elements, or a cohomological
interpretation of `X²-X`. Dependency: `ParityProducts → ParityCoboundary`.

## A45–A48 intake: grading perturbations and existing transport owners

The 2026-10-30 user packet is normalized on the existing associative-ring
PeirceSpine carrier. Its contract uses only `P * P = P`, preserves factor
order, and reuses `Basic`, `Supercharge`, `ChiralEulerFactors`, and
`Homogenized`. The new dependency order is:

```text
ChiralEulerFactors → GradingPerturbation
GradingPerturbation + Homogenized → RingHomTransport
RingHomTransport + Cl11TensorTowerLimit → MatrixColimitTransport
```

`GradingPerturbation` proves the shifted squares, ordered square
factorizations, sandwich identities, commutators, and the exact graded defect
of the proposed unchanged-grading sandwich. For `H = S + Φ`, the defect is
`H*S*H-S = -V*S + 2Φ`; its even projection is `-V*S` and its odd projection is
`2Φ`. In particular, `V=0` alone does not remove the odd contribution. A
sandwich is not automatically conjugation by an invertible element.

`RingHomTransport` proves naturality of the specific polynomial operators
under arbitrary ring homomorphisms, with no unnecessary idempotency assumption
on the naturality lemmas. `MatrixColimitTransport` uses the existing full-matrix
`Cl11TensorTowerLimit.Limit` and its `ofStage` maps: the square law permits
arbitrary amplitudes in the limit, and the four homogenized channels commute
with the actual matrix bonding maps. No new limit carrier is introduced.

Independent source review confirmed broader preexisting infrastructure:
`PeirceDissipatorTrinity` (ring/algebra transport), `PeirceOperatorTower`
(injective towers and compatible cocones), `DirectLimitSuperClosureLemmas`
(actual direct-limit lift and uniqueness), `LieJordanPeirceColimit`
(stage corner transport and a noncommuting limit witness),
`FilteredDirectLimitOwner` (categorical colimit injection/descent/uniqueness),
and `FiniteParityChainMap` (cohomology maps with identity/composition laws).
These are not missing constructions. Connecting the particular
`PeirceSpine.CentralizerCohomology` quotient to an induced homomorphism remains
a distinct carrier-specific task; polynomial naturality alone does not supply
an isomorphism of cohomology groups.

The user's opposite-grade anomaly idea also has an existing owner:
`NCG.AnomalyGradeGeneration.odd_product_anomaly_generates_opposite_grade` and
`odd_product_anomaly_nonzero_iff`. They use the nonassociative operator-valued
Zorn carrier and its ordered `skewCross`, not the associative Peirce ring.
The two results must not be identified by terminology alone.

Content addressing remains separately owned by `DAG.ContentAddressable` and
`DAG.TermDigest`: expression determinism supplies reproducible search keys;
ring-hom naturality does not establish hash injectivity or semantic equality.

Verification of this addition: locked `lake build
InfoGeometry.OperatorAlgebra.PeirceSpine` passed (3192 jobs, mostly cached).
`tests/PeirceGradingTransportAxioms.lean` checked all 54 new declarations:
`map_idempotent` uses no axioms, and the other 53 use only subsets of
`propext`, `Classical.choice`, and `Quot.sound`. The source placeholder scan
found no `sorry`, `admit`, custom `axiom`, or `unsafe`. Independent read-only
review accepted the identities, carrier reuse, and precise colimit scope.
The semantic-vacuity gate reported 25 short-`simp` naturality warnings; the
independent reviewer classified these as non-vacuous compatibility lemmas.
Warnings remain visible; the checker was not weakened. Existing dependency
warnings were replayed by Lake.

## A49–A50: defect parity contract and extracted identities

Source: the user's 2026-10-30 A49–A50 packet. The mathematical contract uses
an arbitrary associative ring, an idempotent P, the existing Peirce projections,
and `Core.IdempotentGraphGrassmannian.idempotencyDefect`. It introduces no
alternate multiplication, commuting carrier, or duplicate defect definition.
The dependencies are `TransferDefect` and `ParityProducts`, not the narrative
A47→A48 numbering: ring-hom transport and colimits are not premises of these
local polynomial identities.

`PeirceSpine/DefectParity.lean` extracts 16 reusable lemmas: parity equivariance;
commutator differentiation of the defect; universal even/odd defect readouts;
odd perturbation square and negative commutator square; a division-free scaled
parity-difference square; Phi/J specializations; ordered parity products;
metric defect readouts; and the two double-derivation mismatch identities.
The exact components are δ(E)+O² and EO+OE−O. The ordered product of P+Phi
with its parity image is P−V−J, correcting the intake's P−V+J sign.

The packet's halves and quarters require invertibility assumptions not present
in an arbitrary ring. Peirce projections supply the decomposition without those
divisions; parity eigenspaces need not distinguish grades in characteristic two.
The function X↦X−σ(X) is an additive parity difference; the supplied statements
do not specify a group-indexed cocycle or establish a Hilbert 90 theorem.
An ordered product Xσ(X) is fixed exactly when X commutes with σ(X), as already
proved by `ParityProducts.parityConj_orbit_product_fixed_iff`. No unconditional
Galois-norm multiplicativity or Galois-extension assertion is introduced.

A49–A50 defect-parity verification completed: the locked PeirceSpine umbrella
build passed (3198 jobs, mostly cached); all 16 declarations passed the
`PeirceDefectParityAxioms.lean` check with foundational axioms only; semantic
vacuity findings were zero, and the placeholder scan was empty. Independent
source review accepted all statements and the corrected ordered-product sign.
The later user packet reuses A49–A50 labels for different transfer/discriminant
and commutator statements. Those are already individually proved in
`GradingTransfer` and `GradingPerturbation`; no duplicate numbered packet was
added. Ring-valued multiplication identities do not assert a vector-space
basis, linear independence, scalar eigenvalues, or a spectral gap.


## A53–A54: corrected integer extraction and cross-charge brackets

Contract (2026-10-30): arbitrary associative ring B, an idempotent P, existing
Peirce corners, and native integer-linear endomorphisms. Reuse SandwichCharge,
EndomorphismCharge, ChargeSectors, CornerChargeSectors, ChargeExtraction,
ChargeExtractionBalances, and CrossChargeBrackets. No duplicate numbered
conjunction packet is introduced. The latter extraction and bracket owners
are now reachable from the PeirceSpine umbrella.

The causal dependency order is corner identities → charge identities →
iterated charge/extraction, and bundled endomorphism charge → sector membership
→ bracket charge addition. Existing PeirceAdjointCycle.ad_cube_eq_ad implies
the quintic on all integer-linear endomorphisms via
EndomorphismCharge.endomorphismCharge_fifth. Narrative stage numbering is not
a theorem dependency.

Corrections to the submitted packet:

- 4D2−D4 = 3(G+1+G−1), and 4D1−D3 = 3(G+1−G−1).
  Their sum/difference isolates 6G±1, without the extra factor 2 in the packet.
- The zero and extremal extraction factors are respectively 4 and 24.
- [G+2,G−2](X) = Q+ X Q− − Q− X Q+.
  Composition reverses the order of right multiplication. The error relative
  to the submitted same-support expression is exactly −V X Sigma.
- The Vandermonde determinant is 288. These are integral scaled extraction
  identities, not an inverse over the integers. Division needs additional
  scalar hypotheses. Charge-sector bracket closure is proved, but directness
  of five eigenspaces in arbitrary characteristic and identification with a
  KKT algebra do not follow from these formulas.

Independent read-only QMS review accepted the corrected mathematical scope
and found no placeholders or hidden commutativity assumptions in the five
reviewed owners. It identified missing required copyright headers, which were
added. The initial locked umbrella plus ChargeExtractionBracketAudit build
passed (3225 jobs, mostly cached); all 16 printed declarations used only
propext and/or Quot.sound. The final locked build passed (3227 jobs), including the umbrella, the
16-declaration axiom audit, and the previously pending PeirceSuperoperatorCharge
and LogarithmicPullback modules. Existing style/deprecation warnings remain.
No placeholders were found in the five reviewed owners.

The semantic gate retained one trivial_surface warning for
endomorphismCharge_apply (rfl). Independent review accepted it as a used
bundled-to-pointwise evaluation compatibility lemma, not a vacuous theorem.
The checker was not changed.

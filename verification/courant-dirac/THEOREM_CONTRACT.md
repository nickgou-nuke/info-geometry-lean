# Cotangent Lie algebra and neutral skew graphs

## Intake, provenance, and scope

Source: the uploaded `Pasted text(20261125-071918).txt`, whose contents were
inspected in this conversation before an execution-environment reset. The
attachment proposed a capstone combining source/target linearization,
cotangent/coadjoint brackets, and opposite skew graphs. The original attachment
bytes are not currently available in the restored workspace. This contract
does not assert byte-preserved source provenance or an attachment checksum.

Repository baseline: `nickgou-nuke/info-geometry-lean` at
`fe24e350b08fdea04f74c0748ef9fd9417c47529`.
Required environment: Lean 4.34.1, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Repository pins remain unchanged.
These identifiers record the checkout baseline. Acceptance of the task's
working changes is bound to the exact source hashes in `VALIDATION.md`.

The source combines correct algebraic identities with stronger geometric
interpretations. The implementation uses native real Lie algebras, the native
coadjoint Lie module, linear maps, submodules, and existing neutral/KKS owners.
Independent source review passed for the versions recorded in
`SEMANTIC_REVIEW.md`, including explicit reconciliation of the proof repairs.
The restored owners were then compiled and audited at the required pins.
`VALIDATION.md` records the focused acceptance results and the separate root
build boundary; source review alone is not a compilation certificate.

## Claim ledger

| Claim | Mathematical contract | Boundary |
|---|---|---|
| Unit difference/midpoint | `poissonSharp α X = -⁅X, α⁆`; source is second projection, target subtracts this drift; identities hold as linear maps | No identification with a smooth groupoid derivative is asserted |
| Cotangent bracket | On `g × Module.Dual ℝ g`, `([X,Y], ad*_X β - ad*_Y α)` is a native Lie algebra and preserves the existing neutral pairing | This is the cotangent double associated with zero cobracket; no general Lie bialgebra construction |
| One-sided bracket | `([X,Y], ad*_X β)` obeys left Leibniz and has the stated explicit symmetric sum | Name it hemi-semidirect; it need not satisfy Courant alternation over a point |
| False prose identity | The diagonal adjoint/coadjoint action preserves the neutral scalar pairing; its derivative is zero, while the hemi symmetric sum can be nonzero | Prove a generic nonzero-readout obstruction and a concrete matrix counterexample |
| Concrete obstruction | In the existing `Mat2R`, take `H = E₀₀`, `E = E₀₁`, and `α(A) = A₀₁`; `[H,E] = E`, and the hemi symmetric sum evaluated at `E` is `-1`, while the proposed pairing derivative is `0` | Full real matrix commutator and an actual algebraic covector; no commuting or scalar substitute |
| Neutral graphs | For `P : Module.Dual ℝ E →ₗ[ℝ] E`, use the actual submodule `range (P.prod id)` | No primal/dual identification is implicit |
| Isotropy and maximality | Isotropy iff evaluation-skewness; under skewness the graph equals its neutral orthogonal | Pointwise linear geometry; the orthogonal theorem explicitly uses dual separation through `Module.Projective ℝ E` |
| Opposite-graph pairing | Under skewness, the cross pairing is `2 * η (P ξ)` | The factor corresponds to the existing unscaled neutral bilinear form; Poisson interpretation needs the appropriate tensor and convention |
| Intersection | The two graphs intersect in the image of `ker P` under `ξ ↦ (0, ξ)` | No skewness is required; the kernel is a space of covectors, not automatically a space of entropy functions |
| Splitting | Disjointness iff injectivity; spanning iff surjectivity; complementarity iff bijectivity | In finite equal dimensions, these give the familiar invertibility criterion |
| Matrix specialization | Use native `dotProductEquiv` to identify coordinate vectors with dual covectors and `Matrix.toLin'` for multiplication | Actual finite matrices over any finite index type, including `Fin n`, without a scalar or commuting replacement |

## Carriers, operations, and conventions

The common carrier is the existing primal-first
`PhaseSpaceCarrier E = E × Module.Dual ℝ E`. Its bilinear form is

```text
B((x, ξ), (y, η)) = ξ(y) + η(x).
```

The native coadjoint action satisfies

```text
⁅X, α⁆ Y = -α ⁅X, Y⁆.
```

Consequently, `poissonSharp α X Y = α ⁅X, Y⁆`, in agreement with the existing
algebraic `SouriauKKS.kksForm`. The source/target models have the formulas

```text
unitSource (X, δα) = δα
unitTarget α (X, δα) = δα - poissonSharp α X.
```

For a dual-to-primal linear map `P`, evaluation-skewness means
`ξ (P η) = -η (P ξ)`. The opposite-graph pairing then equals `2 * η (P ξ)`.
The neutral graph theorem is distinct from the existing symmetric Legendre
graph results for a symplectic form.

The matrix adapter uses the explicit linear equivalence

```text
coordinatePhase (u, ξ) = (u, dotProductEquiv ℝ ι ξ)
matrixSharp P = (Matrix.toLin' P).comp (dotProductEquiv ℝ ι).symm.toLinearMap.
```

Thus `matrixSharp P (dotProductEquiv ℝ ι ξ) = P *ᵥ ξ`, and the coordinate
neutral form is `dotProduct u η + dotProduct v ξ`. No unrecorded identification
of a vector with a covector is used.

## Existing owners and hypotheses

- `InfoGeometry.Clifford.NeutralPhaseSpaceCore`: `PhaseSpaceCarrier`,
  `canonicalNeutralBilin`, `canonicalNeutralBilin_apply`, and nondegeneracy.
- `InfoGeometry.Canonical.SouriauKKSForm`: `SouriauKKS.kksForm` and its skew law.
- `InfoGeometry.Algebra.FiniteSpinAlgebra`: the existing full matrix carrier
  `Mat2R = Matrix (Fin 2) (Fin 2) ℝ` for the obstruction witness.
- Mathlib `Module.Dual.lie_apply` and native `LieModule` provide the coadjoint
  representation. No standalone bracket/Jacobi assumption packet is introduced.
- The cotangent `LieRing` and `LieAlgebra` are explicit named constructions,
  not competing global instances on the product carrier.
- Mathlib `LinearMap.range`, `LinearMap.ker`, `Submodule.orthogonalBilin`, and
  `dotProductEquiv` supply the actual graph, kernel, orthogonal, and coordinate
  maps.
- Mathlib's associative-ring Lie structure supplies the actual matrix
  commutator in the concrete obstruction section.
- The neutral owner transitively imports `Mathlib.Tactic` through the unchanged
  `FiniteSpinAlgebra` owner. This inherited import is part of the declared
  validation footprint.

The previously performed bounded owner search covered `lean/InfoGeometry`,
relevant documentation, Mathlib Lie/dual/graph interfaces, and the two closest
sources from PR #444. That PR was observed closed and unmerged during the
original inspection; no dependency on its branch was introduced. This search
record is historical task evidence and does not assert current remote state.

## Proof dependency order

1. Native Lie algebra and coadjoint representation imply cotangent and
   hemi-semidirect identities.
2. Native evaluation pairing implies invariance and the obstruction to the
   proposed symmetric-part interpretation.
3. Matrix units and the existing full matrix carrier provide a concrete
   nonzero instance of that obstruction.
4. Existing KKS evaluation determines the algebraic unit maps and stabilizer.
5. Linear range and evaluation-skewness imply graph isotropy, maximality, and
   cross pairing; the opposite-graph kernel and splitting results hold without
   skewness.
6. Native coordinate duality specializes the graph statements to matrices.

## Claims not established

No implication from these algebraic results to smooth cotangent groupoids,
Courant algebroid integrability, general Drinfeld doubles, or entropy-Casimir
identification is claimed.

In particular:

- `unitSource` and `unitTarget` are algebraic linearization models. Identifying
  them with `fderiv` or `mfderiv` requires a smooth groupoid construction and
  derivative theorem.
- The cotangent semidirect bracket is the double for a zero cobracket. A
  general Lie bialgebra double requires its additional dual bracket and
  compatibility data.
- A pointwise skew graph is maximally isotropic. A variable bivector graph is
  an integrable Dirac subbundle only after the corresponding differential
  condition is proved.
- Opposite graphs need not be complementary when their map has a kernel.
- Casimir differentials lie in the Poisson kernel under the Casimir
  condition. No arbitrary entropy function is proved to satisfy that condition.

## Acceptance

Compile complete sources with warnings treated as errors at the exact pins.
Audit every module-owned declaration, including generated declarations, with
`Lean.collectAxioms`; allowed foundations are only `propext`, `Classical.choice`,
and `Quot.sound`. Run independent source/scope review, the repository staged
proof gate, and the narrow root build wrapper. Report an isolated pinned-source
build separately from any root dependency/configuration obstruction. Preserve
the shared build lock and all existing caches.

The source-review record preserves the exact versions inspected before the
environment reset. After reconstruction, compare source hashes or perform
independent review of any differences. Do not treat the prior source review
as proof of compilation or of equality with a reconstructed source file.

## References for terminology

- Liu, Weinstein, Xu, *Manin triples for Lie bialgebroids*,
  <https://arxiv.org/html/dg-ga/9508013v3>.
- Li-Bland, Meinrenken, *Courant algebroids and Poisson geometry*,
  <https://www.math.toronto.edu/mein/research/cour.pdf>, Definition 1.1 and
  Examples 1.2–1.3.

# Real-number quantum theory: theorem contract

## Source and existing owners

Intake: Timothée Hoffreumon and Mischa P. Woods, *Quantum theory does not
need complex numbers*, arXiv:2504.02808v2, 9 October 2025. The attached PDF
is the source version for this task. The implementation base is upstream
`c143c264bc18bbf41d692be4e270b5b7f7405702`.

Attached PDF SHA-256:
`8254e9db113c13c3f76c47b936b28bf736cb3fd0dfc61ec5a80793791bcf9b68`.

Existing source owners inspected before implementation:

- `Quantum/RealKCategory.lean`: arbitrary real vector spaces with an internal
  square-minus-one endomorphism, intertwiners, and an equivalence with complex
  modules. Its `K_sq` field is the defining input, not a derived physical law.
- `Canonical/Cl11JordanComplexRealificationBridge.lean`: the concrete
  `Matrix (Fin 2) (Fin 2) ℂ` realification and its exact commutant.
- `Signal/ComplexRealification.lean`: arbitrary finite-index paired real
  vectors and the real part of their Hermitian pairing.
- `Quantum/ChoiCompletePositivity.lean` and `Quantum/KrausBoundaryDuality.lean`:
  the actual finite Kraus map and its positivity/trace theorems.

The missing matrix step is a dimension-independent realification with native
`Matrix.PosSemidef`, ordinary trace, normalized states, and a proved tensor
composition law. The missing categorical step is the tensor construction
balanced with respect to the already-owned internal complex structures.

## Carriers and conventions

For arbitrary finite index types, use the full complex matrix algebra and
real block matrices indexed by `n ⊕ n`. No diagonal, scalar, or mutual
commutation assumption is imposed on input matrices.

`Γ(A) = [[Re A, -Im A], [Im A, Re A]]`.

The input algebra multiplication is the native matrix multiplication.
The real complex structure is `J = Γ(i I)`. It commutes with the image
of Γ; centrality in the entire real matrix algebra is neither assumed nor
claimed. The adjoint is `Matrix.conjTranspose`; on real entries it is transpose.

The state encoding is `state(ρ) = (1/2) • Γ(ρ)`. The effect encoding is
`Γ(E)`. These are distinct because `trace (Γ A) = 2 * Re (trace A)`.

## Intended dependency order

1. Rectangular block embedding and inverse on its image.
2. Full noncommutative multiplication and adjoint compatibility.
3. Internal J and exact image/centralizer characterization.
4. Vector action and Hermitian pairing, using the existing paired-vector owner.
5. Preservation and reflection of `Matrix.PosSemidef`.
6. Ordinary trace, normalized states, Born readout, and Kraus transport.
7. Aligned tensor composition and its state normalization.
8. Tensoring objects and morphisms in the existing real K category.
9. Explicit coordinate isomorphism and matrix-action naturality in the existing
   real K category.
10. The full real tensor-carrier phase projector and positivity of its compression.

These are mathematical dependencies, not interpretations inferred from names.
The implementation and audit files determine which targets are closed.

## Acceptance statements

- Γ is injective and respects products, sums, real scalars, identity, and adjoint.
- `A.PosSemidef ↔ (Γ A).PosSemidef`.
- A positive trace-one complex matrix encodes to a positive trace-one real matrix.
- Every positive trace-one real matrix commuting with J has a unique complex
  density preimage, using `density_preimage` and `state_injective`.
- `trace (Γ E * state ρ) = Re (trace (E * ρ))`, without `Commute E ρ`.
- `trace (state ρ * state ρ) = (1/2) * Re (trace (ρ * ρ))`.
- The aligned tensor is Γ of the complex Kronecker product on encoded inputs;
  its mixed-product law preserves the order of both noncommuting factors.
- The tensor of normalized local encodings requires one compensating factor 2.
- The real K tensor satisfies `K x ⊗ y = x ⊗ K y`, and tensor maps are
  constructed from the existing intertwiner maps.
- The matrix action agrees with the existing complex-to-real-K functor through
  an explicit coordinate isomorphism.
- `P = (I - J ⊗ₖ J)/2` is a symmetric idempotent, and `P (A ⊗ₖ B) P` is
  positive semidefinite for every pair of positive semidefinite real inputs.

## Implemented owners

All paths below are under `lean/InfoGeometry/Quantum/`. The audit inventory
counts public definitions and theorems, not only substantive theorem statements.
The existing `InfoGeometry.All` umbrella imports `RealificationAudit`, exposing
all seven owners and their audit through the established public entry point.

| Owner | Public declarations | Verified surface |
| --- | ---: | --- |
| `Realification.lean` | 28 | Rectangular block embedding; injectivity; real linear and ring maps; ordered multiplication; adjoint; exact J-centralizer image |
| `RealificationStates.lean` | 23 | Vector action and pairing; Hermitian and PSD equivalences; normalized density correspondence; Born readout; ordinary purity scaling |
| `RealificationChannels.lean` | 9 | POVM transport; Kraus transport and completeness; encoded density preservation; an existing spin noncommutativity witness |
| `RealificationTensor.lean` | 23 | Independent real block tensor formula; ordered mixed products; compatible-sector positivity; normalized product states; local actions and product Born readout |
| `RealKTensor.lean` | 19 | Tensor objects over the existing derived complex action; real bilinearity; K balance; morphism extensionality; tensor-map identity and composition |
| `RealificationCategory.lean` | 13 | Actual J-based coordinate object; rectangular intertwiners; coordinate isomorphism and matrix-action naturality |
| `RealificationCompression.lean` | 14 | Full-carrier phase involution and projector; real bilinearity and unrestricted PSD compression |
| `RealificationAudit.lean` | 129 audit commands | Exact public-declaration axiom inventory for all seven implementation owners |

## Scope boundaries and source corrections

Hermitian matrices are not an associative algebra: their full matrix algebra
is the algebra owner, and the Hermitian part is a real linear/Jordan sector.
The real encoding preserves measurement statistics but rescales ordinary
trace-square purity by 1/2. This is not a theorem that extreme points cease
to be extreme in the restricted compatible state space. A set complement of
the J-centralizer is not its
anticommuting sector. The latter must be defined by an actual linear
projection/direct-sum condition.

The ordinary real tensor product of the full centralizer algebras has the
wrong dimension for the claimed aligned algebra equivalence. The categorical
construction therefore balances the derived complex action. The paper's
Hermitian-space real tensor claim and its extension to all real matrices
are distinct statements.

Appendix E's unrestricted composition is a positive compression with a
kernel, not a multiplicative tensor equivalence on every real matrix. Its
D8 matrices are unital on a projector's image, not on the full ambient
space. No full ambient D8 representation, full monoidal coherence package,
infinite-dimensional completion, or experimental no-go theorem follows
from the finite algebraic results in this implementation.

The total `alignedTensor` fallback is defined by reconstruction from the first
block column and can fail to preserve positivity outside the compatible
sector. It is a different operation from Appendix E's positive compression
on the larger real tensor space. The fixed two-by-two predecessor retains
its existing implementation; a direct reindexing theorem to that owner is
not part of this change.

The compression owner does not yet prove an isometry/reindexing equivalence
between the full projector image and the reduced `alignedTensor` carrier.
It also makes no trace-normalization or rank claim for the compression.

## Verification

The root Lean toolchain and dependency pins remain unchanged: Lean 4.34.1,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Compilation used the
shared repository build lock through `verification/rnqt/check.py`. That focused
Lake project imports the canonical source files and retains the exact Mathlib
dependency closure; it does not replace the root package or its push gate.

Executed on 11 November 2026:

1. `python3 verification/rnqt/check.py build` — exit 0, all seven owners and
   `RealificationAudit` compile (3384 Lake jobs, including reused dependencies).
2. `python3 verification/rnqt/check.py env lean <absolute-path-to-RealificationAudit.lean>`
   — exit 0, fresh audit elaboration. All 129 expected declarations appear
   exactly once; their axiom dependencies are subsets of `propext`,
   `Classical.choice`, and `Quot.sound`. No `sorryAx` appears.
3. `python3 tools/infra/opengauss_cli.py refute <eight-new-Lean-files> --strict`
   — exit 0, zero traps in every file.
4. `python3 tools/infra/opengauss_cli.py review <eight-new-Lean-files> --gate GATE_4 --json`
   — exit 0, `STATIC_REVIEW_PASSED_KERNEL_UNVERIFIED` for every file. This is
   the static tool's actual verdict; kernel verification is supplied separately
   by steps 1 and 2.
5. `python3 tools/quality/semantic_vacuity_gate.py <eight-new-Lean-files> --fail-on warning`
   — exit 1, 22 `trivial_surface` warnings. Independent source review found
   them to be coordinate/application equations, consequences of proved algebra
   laws, and zero/bilinearity helpers. There are no other finding categories.
   Correct `rfl`/`simp` API proofs have not been expanded to evade this lexical
   heuristic. This result is not reported as a warning-free scan.
6. `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Quantum.RealificationAudit`
   — exit 1 while loading the root package: the configured
   `external_refs/homotopy-hypothesis-lean4` directory is absent.

The read-only root path preflight also reports absent
`external_refs/atlas-lean` and an uninitialized `GIFT` gitlink. The first two
path entries have no authoritative source/revision in the root manifest;
inventing replacements or resolving them to moving branches would not repair
provenance. No root dependency, hook, or quality gate was weakened.

The independent A-A and QA-A dispositions, staged/commit checks, and exact
pre-push result must accompany the final delivery. A successful focused build
is not a whole-repository build, an `InfoGeometry.All` build, or a publication
certificate. The umbrella integration adds only an import; its full root
compilation remains subject to the same dependency-loading boundary.

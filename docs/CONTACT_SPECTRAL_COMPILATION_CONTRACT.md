# Contact poles, normalized spectral pairing, and finite heat supertraces

## Intake and scope

Task: compile the supplied Apollonian–Möbius–Witten stream into native Lean 4
mathematics and publish an upstream draft PR. The unchanged intake is preserved
in `docs/intake/CONTACT_SPECTRAL_2026_11_16.md`. Its statements are proposals,
including its opening reference to a previously proved permanent obstruction;
that obstruction was not proved in PR #360 and is not assumed here.

Base: PR #360, branch `feat/sp4-contact-curvature`, commit
`01cc888565824d2a5f275b28cb33187a28ec6e73`. This PR is stacked on that branch
because it uses the constructed native `Sp4Contact` owner.

The machine contract and discovery receipt are in
`docs/contracts/contact-spectral-compilation.json` and its companion
`contact-spectral-compilation-discovery.json`. Discovery is navigation evidence;
the declarations and their checked proofs determine the mathematical scope.

## Claim ledger

| Intake atom | Correct statement and disposition |
| --- | --- |
| Opposite extreme grades are reciprocals | For the normalized concrete matrices `E = E14`, `F = E41`, all four Moore–Penrose equations hold. Both are nonzero square-zero matrices and are not units. Arbitrary opposite-grade scalar multiples require normalization; they are not automatically mutual generalized inverses. |
| The two support projectors do not commute | Counterexample to the prose: `EF = E11`, `FE = E44` are distinct orthogonal commuting star projections. `E` and `F` themselves do not commute. |
| Pole exchange forces an ambient square of minus identity | The existing Weyl unit completed by identity on the middle plane has square `I - 2P`, where `P = E11 + E44`. Choosing `S = -omega` additionally rotates the middle plane and gives `S² = -I`. These are different operators. |
| A folding average has defect minus half identity | For the completed endpoint Weyl operator the defect is `-P/2`; for the explicitly chosen full rotation it is `-I/2`. |
| Nonzero modes pair only when their eigenvalue is positive | The existing algebraic owner pairs `AB` and `BA` at every nonzero eigenvalue. For an adjoint/Hilbert pair, normalize the existing equivalence at a positive real eigenvalue. The new native `LinearIsometryEquiv` takes positivity as an explicit hypothesis and reuses the existing continuous equivalence and norm law. |
| The anticommutator is automatically positive | Positivity requires an adjoint/Hilbert model. General off-diagonal maps alone do not supply it. |
| Noncompactness forces a heat-index anomaly | Not a theorem. Trace existence, domains, boundary conditions, and regularization must be specified. Prove instead the actual finite-matrix identity `trace(J * exp(t • Q²)) = trace J` under `JQ = -QJ`, using the native convergent matrix exponential. |
| Zero index eliminates zero modes | False. Construct the self-adjoint odd full-matrix supercharge `Q = E + F`; its kernel is the middle plane and its balanced heat supertrace is zero. Compare a balanced invertible supercharge with the same zero heat supertrace. |
| The Green operator is globally `(Q²)⁻¹Q` | An inverse on the kernel is unavailable. Reuse the four Penrose equations; the concrete tripotent `Q` is its own Moore–Penrose inverse and `Q²` is its support projector. No unbounded Fredholm theorem is inferred. |
| An integrated scale derivative equals an APS eta correction | Unsupported without a particular elliptic/boundary realization and the correct normalization and kernel terms. No APS, Callias, KMS continuation, or scattering theorem is promoted. |
| Order four means a fourfold spin cover or physical fermion parity | Unsupported interpretation. A matrix order and a covering degree are different data; no spin/metaplectic representation is constructed. |
| The diagram proves universal necessity and uniqueness | The supplied graph has the same 15 vertices and 28 covers as `ContactDependencyPoset`. Reuse that exact order, relabeling `bianchi` as the present spectral-splitting label in prose. Its terminal join is a fact about that order, not a proof of semantic uniqueness. Its height is strictly increasing but is not a cover-rank function; it is not a lattice. |
| Every obstruction stage remains nonzero in a colimit | No directed system or transition maps are supplied. No colimit nonvanishing claim is made. |

## Exact carriers and conventions

- Contact calculations use `Sp4Contact.Mat = Matrix (Fin 4) (Fin 4) ℝ`, with
  ordered multiplication and the native matrix star. `Sp4Contact.Sp` is the
  already constructed Lie subalgebra. Products need not belong to that Lie
  subalgebra; the four Penrose equations are proved in the ambient matrix ring.
- Matrix indices in Lean are zero-based. `E14` denotes the matrix with its
  only nonzero entry at `(0,3)`. The fixed alternating form is the one in
  `Sp4Contact.omega`; no different symplectic convention is substituted.
- Hilbert pairing uses bounded continuous linear maps between complete real or
  complex inner-product spaces. The eigenspaces are Mathlib submodules.
  Normalization uses the positive real square root, with positivity an explicit
  hypothesis. This does not assert an eigenbasis or pure point spectrum.
- The heat result uses arbitrary finite real matrices and the existing parity
  supertrace owner. The exponential is `NormedSpace.exp`, not a formal symbol,
  assumed heat trace, or finite truncation. No infinite-dimensional trace is
  introduced by this result.
- The explicit kernel example uses `γ = diag(1,1,-1,-1)`. The contact grading
  element `diag(1,0,0,-1)` is not this global chirality involution.

## Owner reuse and smallest gaps

The existing `Singular.MoorePenrose` predicate contains the four equations.
`SquareZeroMoorePenrose`, `MoorePenroseSquareZero`, and `Core.PeirceWeylUnits`
already prove generic support, nilpotency, and Weyl laws. The new contact owner
must construct their hypotheses for the actual endpoints and prove the exact
full-space readouts. It must not copy the generic API.

`OperatorAlgebra.PartnerEigenspaces` and `PartnerGeneralizedEigenspaces`
already construct genuine nonzero partner equivalences.
`Analysis.HilbertGramDuality` additionally constructs the bounded Hilbert
equivalence and proves its norm scaling. The missing refinement is its
normalization as a native linear isometry equivalence.

`OperatorAlgebra.FiniteParitySupertrace` proves graded trace cyclicity.
`Canonical.SpinorialCore.FiniteSupertrace` already proves the rectangular
polynomial identity, and `Canonical.SpinorialCore.FiniteIndex` owns the native
kernel/cokernel index and its dimension-difference theorem. Reuse these owners;
connect the index to the actual adjoint-kernel difference using Mathlib's
equality of adjoint ranks and rank-nullity.
The finite-index owner's unused import of `SpinorialCore.Algebra` pulled the
entire `Mathlib` umbrella into this small theorem surface. Replace that import
with the precise finite-dimension, matrix-trace, and arithmetic tactic imports;
preserve its definitions and theorem statements. Its existing counting proof
now explicitly substitutes the helicity hypothesis and casts the natural-number
handshaking relation into the integer domain with `zify`. This makes the actual
use of both necessary hypotheses visible to the strict source screener.
Review its direct consumers
for reliance on the former transitive export before promotion.
The source review found four existing direct consumers: `SpinorialCore.All`
imports `Algebra` directly; `SpinorialCore.FiniteSupertrace` imports `Bipartite`,
which imports `Algebra`; both `InfoGeometry` and `AllExhaustive` independently
import `SpinorialCore.All` and `Bipartite`. Each retains the former import
surface. Unknown external clients that relied on incidental re-exports may
need explicit imports. Only the active `lean/` owner is changed; the legacy
`src/` copy is outside this task.
`Analysis.PairedHeatTrace` proves cancellation for supplied convergent paired
spectral sums. The missing finite operator result derives cancellation for the
native matrix exponential directly from oddness, without assuming a spectral
expansion or equality of traces.

## Actual dependency order

1. Construct the endpoint Penrose pair and square-zero facts from `Sp4Contact`.
2. Apply existing support/Weyl theorems; compute full-space matrices and folding
   defects. Independently normalize the existing Hilbert Gram equivalence and
   identify the native finite index with the adjoint-kernel dimension difference.
3. Derive trace cancellation of positive even powers from graded cyclicity;
   pass through the convergent exponential series to the heat supertrace.
4. Apply that theorem to explicit odd contact supercharges and prove their
   different kernel behavior. Keep the supplied finite narrative graph separate
   from these proof dependencies.

## Roles and acceptance

Generation: root and `endpoint_candidate`, with candidates outside the promoted
source tree. Independent mathematical/source audit: `audit_math`; the later
proof-only corrections are reviewed by `scalar_audit`. The unchanged native
compiler and all-declaration axiom verifier run in the primary session against
a fresh source snapshot. Independent evidence review and source-gate execution:
`acceptance_qa`. These execution and review roles are recorded separately.

Use pinned Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`; serialize all compiler runs through
the shared build lock. No proof holes, custom axioms, `native_decide`, gate
changes, or dependency changes are permitted. Record final commands, warnings,
source hashes, axiom footprint, and the actual root publication-gate outcome
after verification. The prior missing root path dependency is not a certificate
of failure or success for the new source; scoped checks and root checks remain
separate evidence.

## Open scope

No manifold compactification, spin-cover classification, metaplectic action,
unbounded Dirac domain, APS/Callias index theorem, continuum spectral splitting,
KMS analytic continuation, scattering correction, or obstruction colimit is
constructed. These require additional definitions and hypotheses, and some
universal claims in the intake are false as stated.

## Primary literature for the analytic boundary

- E. Witten, [Constraints on Supersymmetry Breaking (1982)](https://web2.ph.utexas.edu/~vadim/Classes/2025f/Witten1982.pdf),
  Sections 1–2: the index must vanish for breaking to be possible; vanishing is
  not a proof that breaking occurs.
- X. Dai and J. Yan, [Witten deformation on non-compact manifolds: heat kernel
  expansion and local index theorem](https://doi.org/10.1007/s00209-022-03150-0),
  Propositions 2.4 and 5.1: suitable noncompact settings have trace-class heat
  operators and a time-independent supertrace. Noncompactness alone does not
  force a scale anomaly.
- M. F. Atiyah, V. K. Patodi and I. M. Singer, [Spectral asymmetry and Riemannian
  geometry I](https://doi.org/10.1017/S0305004100049410): the boundary problem,
  eta normalization, and kernel correction are additional data, absent from
  the proposed universal UV/IR equation. These citations guide the scope audit;
  they are not inputs accepted as Lean proof terms.

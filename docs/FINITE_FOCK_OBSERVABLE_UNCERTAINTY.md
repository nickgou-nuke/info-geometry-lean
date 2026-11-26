# Finite real Fock observables and uncertainty

## Theorem contract

This follow-up connects the quadratic creation–contraction operators discussed
in the supplied CAR/exterior-lift note to the real observable uncertainty
theorem in PR #462. Its carrier is the existing
`InfoGeometry.Clifford.SpinorSpace (Vector n)`, with the positive inner product
induced by `fockCoordinates n` in `FiniteRealFockMetric`.

For a real matrix `M : Matrix (Fin n) (Fin n) ℝ`, define the actual continuous
operator

```text
Q(M) = ∑ i, ∑ j, M i j • (C_i ∘ A_j),
```

where `C_i = fockExtActionCLM n i` and `A_j = fockIntActionCLM n j` are the
existing bounded creation and contraction maps. Composition is creation after
contraction on every exterior degree. No commutation of distinct observables
or diagonal form of the coefficient matrices is assumed.

The first proved identity is `adjoint (Q(M)) = Q(M.transpose)`, derived from the proved
creation/contraction inner-adjoint identity. Thus symmetric coefficients give
Hilbert-self-adjoint observables, while skew-symmetric coefficients give
skew-adjoint operators. Completeness comes from the actual finite exterior
basis and Mathlib's finite-dimensional completeness theorem.

The uncertainty theorem uses the existing `NuclearDoubledConfiguration.pairedLift`,
which preserves ordered composition and Hilbert adjoints and commutes with
the real phase operator. For symmetric real matrices `M` and `N`, put
`A = pairedLift (Q(M))`, `B = pairedLift (Q(N))`, and
`u = A ψ - a • ψ`, `v = B ψ - b • ψ`. The proved inequality is

```text
⟪u, v⟫² + (1/4) ⟪Iop ψ, (A ∘ B - B ∘ A) ψ⟫² ≤ ‖u‖² ‖v‖².
```

This is an application of `PhaseObservableUncertainty.centered_robertson_schrodinger`
after proving its concrete operator hypotheses. It retains both ordered
products. The shifts are arbitrary real numbers; the bound requires no state
normalization. The underlying positive Hilbert adjoint is distinct from a
general indefinite Krein adjoint.

## Existing owners reused

- `Clifford/FiniteRealFockMetric`: the exterior-basis positive metric.
- `Clifford/FiniteRealFockAdjoint`: creation/contraction inner adjointness.
- `Clifford/FiniteRealFockNormBounds`: bounded coordinate operators.
- Mathlib exterior bases, finite-dimensional completeness, matrices, finite
  sums, and continuous-linear-map adjoints.
- `Physics/NuclearDoubledConfiguration`: faithful componentwise doubling,
  adjoint transport, ordered composition, and real phase compatibility.
- `Canonical/PhaseObservableUncertainty`: the positive Gram-derived
  covariance-plus-commutator inequality.

## Boundaries

The generic identity `exteriorLift T = ∑ j, c_(T b_j) a_(b.coord j)` and its
Para-Kähler, Clifford, and Zorn transports are being developed separately.
This follow-up does not copy that unpublished work or claim a checked equality
between `Q(M)` and the generic `exteriorLift` API.

The finite Fock result supplies neither an infinite-mode second-quantization
domain theorem nor a continuous-wavelet admissibility/Plancherel theorem.
The existing algebraic Fock–Zorn linear equivalence also needs a compatible
positive metric before an uncertainty bound can be transported through it.

## Validation

Status: **[kernel_verified]** for the two finite Fock owners below, with the
scope boundaries above retained.

The maintained source-closure compiler and native declaration axiom auditor
passed on 2026-11-26. Environment: Lean `4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. This follow-up is based on
`ed3b8e22b61aff0d75ab79525c18779eb01454b0` from PR #462 and adds the two finite
Fock owners listed below. Their verified source hashes identify the accepted
mathematical snapshot. The follow-up targets PR #462's
`formalize/real-phase-observable-uncertainty` branch because that branch
supplies the required real uncertainty core.

| Check | Observed result |
| --- | --- |
| Complete selected repository source closure | 72 modules verified: 60 reused after source/dependency/artifact fingerprint checks, 12 freshly compiled |
| `Clifford.FiniteRealFockQuadraticAdjoint` | Fresh compilation passed; 0 warnings; all 16 owned declarations audited |
| `Canonical.FiniteRealFockObservableUncertainty` | Fresh compilation passed; 0 warnings; its 1 owned declaration audited |
| Transitive axiom footprint of all 17 new declarations | Only `propext`, `Classical.choice`, and `Quot.sound` |
| Existing dependency warnings in the closure | 52; zero-warning status applies only to the two new owners |
| Strict placeholder scans | 0 findings in either new owner |
| Tracked staged proof gate | Passed |
| Strict semantic-vacuity scanner | 1 `trivial_surface` warning for the used `fockQuadraticCLM_apply` evaluation lemma; reviewed independently as a legitimate definitional API, not mathematical vacuity |
| Independent receipt review | All 72 current source hashes, both selected-owner results, the declaration counts, and all four verifier-helper hashes match the receipt |

The strict semantic scanner therefore exits nonzero; its single finding is
reported rather than suppressed. The substantive adjoint and uncertainty
proofs receive no semantic-vacuity findings. Two unused zero/additivity helpers
were removed to keep the owner focused.

Exact validation command, run from the checkout root:

```sh
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/012eca46cbbe/tmp/mathlib \
  --lean /workspace/scratch/012eca46cbbe/tmp/toolchain/lean-4.34.1-linux/bin/lean \
  --output /workspace/scratch/164a0537dc6c/finite-fock-report \
  --target InfoGeometry.Clifford.FiniteRealFockQuadraticAdjoint \
  --target InfoGeometry.Canonical.FiniteRealFockObservableUncertainty \
  --incremental
```

The output contains `report.json`, `axioms.log`, the generated native audit,
source snapshots, and hashed evidence. Its `seed-evidence` directory preserves
the origin of reused compilation artifacts. Reusing individual successful
artifacts does not adopt the separate CAR transport run's overall status.

Selected source SHA256 values:

| Owner | SHA256 |
| --- | --- |
| `Clifford.FiniteRealFockQuadraticAdjoint` | `cc93dee71895586f52413ca70082cf69360714a19e72d344bdfb612b9e27b3ed` |
| `Canonical.FiniteRealFockObservableUncertainty` | `7453f9a5d3861135235b78892878cf2a16ba4f29480177a1d2e4160429f1b462` |

This is a focused source-closure certificate, not a whole-repository or native
package-integration certificate. The native package build previously stopped
at the missing `external_refs/homotopy-hypothesis-lean4` dependency, which
remains absent. It was not repeated for these additions. No dependency pins
or gate implementations were changed.

PR #462's hosted focused check is separate from this follow-up:
<https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45790367873>.
It passed for the original uncertainty core. The local source-closure receipt
above separately certifies the finite Fock follow-up. The existing hosted
workflow selects the original three core owners; it does not provide a hosted
certificate for the two new finite Fock owners.

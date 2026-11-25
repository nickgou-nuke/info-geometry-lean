# Real Dirac, spin Casimir, and associative Nambu packet

## Publication and provenance

The user requested PR publication on 2026-11-24 after the prior packet remained
`QA_BLOCKED`. The previous scratch checkout and its unpublished commits were
unavailable in the publication runtime. All four new Lean sources were recovered
byte-for-byte from retained source snapshots and checked against their recorded
SHA-256 hashes. This establishes source identity, not kernel verification.

This PR is stacked on PR #429 at
`200d162d7cd8187c7e054ed3bf81b2b93cee235a`, branch
`codex/real-pauli-pfaffian-frame-volume-20261123`. Its kernel is a different
implementation from the lost unpublished base. The shared matrix definitions,
coordinate conventions, and consumed lemmas were inspected directly. Two helper
lemmas are added to that existing kernel: `pauli_add` and
`diracVector_anticomm`. Three recovered sources remain unchanged. The proof of
`RealDiracLinearLift.timeGamma_isAlt` now states its real scalar self-pairing
explicitly before invoking `ring`, after the source gate flagged the implicit
scalar reduction. Its native form, hypotheses, definitions, and theorem statement
are unchanged. This proof repair has separate independent source review.

PR #429 also contains independently authored Dirac, doubled-spin, and Nambu
bridges. This packet preserves the recovered API; equivalence between the two
APIs is not established here. This PR does not recover or certify the missing
earlier Gram-soldering and phase-frame integration.

## Exact intent and theorem boundaries

The packet uses native real matrices, linear maps, bilinear forms, submodules,
Lie adjoints, and the existing associative Peirce cubic. Its scope is finite
algebra, with named ring/module hypotheses in the generic statements.

1. **Faithful Dirac lift.** On `Fin 4 → ℝ`, use the existing `Matrix4` Dirac
   vector and `q(t,x,y,z) = t² - x² - y² - z²`. The proposed identities are
   `D(v)² = -q(v) I` and
   `D(u)D(v) + D(v)D(u) = -2 (u₀v₀-u₁v₁-u₂v₂-u₃v₃) I`.
   The map is injective, and signed trace polarization recovers that pairing.
2. **Specified spinor form.** The alternating form has matrix `timeGamma`.
   Its pullback is `D(v)ᵀ timeGamma D(v) = q(v) timeGamma`. For null `v`,
   the Dirac image is pairwise isotropic for this form and is contained in
   the endomorphism kernel. No arbitrary-form or maximal-isotropy conclusion
   follows from square-zero alone.
3. **Real spin generators.** `Jᵢ` is minus one half of the spatial bivector,
   `Kᵢ` is one half of the time-spatial product, and `ω` is the existing real
   phase. The signs include `ωKᵢ = -Jᵢ`, `Jᵢ² = -I/4`, `Kᵢ² = I/4`,
   `ΣJᵢ² - ΣKᵢ² = -3I/2`, and `ΣJᵢKᵢ = -3ω/4`.
4. **Doubled carrier.** On matrices indexed by `Fin 4 ⊕ Fin 4`, use phase
   `diag(ω,ω)`, cut `diag(I,-I)`, and the off-diagonal identity mirror.
   The chiral supports are `Aᵢ = diag(0,Jᵢ)` and `Bᵢ = diag(Jᵢ,0)`.
   Their Casimirs are `-3P₋/4` and `-3P₊/4`. The doubled mixed Casimir is
   **`-3 cut * phase / 4`**. The commutation claims concern the stated total
   `J` and `K` generators, not the center of the ambient matrix algebra or a
   classification of the real Lorentz Lie algebra.
5. **Associative alternating cubic.** Reuse
   `PeirceSpine.alternatingProduct3`. Under the stated cyclic commutator
   hypotheses, the cubic equals the sum of squares. Regular left multiplication
   on the right module and the adjoint Leibniz derivation remain distinct;
   left multiplication is Leibniz exactly when its coefficient is zero.
6. **Null submodules and counterexamples.** Square-zero sandwich ranges and
   idempotent Peirce 10 ranges have zero pairwise product, trace pairing, and
   cubic. The six regressions retain the 2×2 counterexample to overstrong
   right-ideal trace isotropy and the 3×3 counterexample to the Filippov identity.
   The latter has `(A,B,U,V,W) = (E11,E12,E11,E13,E21)` in one-based notation,
   with left side `E13` and right side zero.

No physical interpretation, complex scalar carrier, topology, colimit,
completion, or representation classification is supplied by these finite
identities.

## Reused owners and dependency order

The existing kernel imports `GullDoranPseudoscalarBridge` and
`MajoranaPfaffian4`. The algebra owner imports
`PeirceSpine.AlternatingCornerTriple`, `NonAssocDerivation`, and
`PeirceMatrixPerfectPairing`. `RealDiracSpinCasimir` imports the kernel and
the algebra owner. `RealDiracNambuChecks` imports the linear lift and spin
owner. The new helpers stay in the kernel owner rather than creating a second
matrix representation.

The additional hypotheses for the two helpers are only their eight real
coordinates. `pauli_add` expands the existing linear combination;
`diracVector_anticomm` checks the existing 4×4 multiplication polynomial.
Their proof scripts are new source, with fresh validation required.

## Recovered source hashes

| Canonical file | SHA-256 before publication changes |
|---|---|
| `lean/InfoGeometry/Algebra/AssociativeNambuOperators.lean` | `ee5391ef087f499cfbbb2fb30bb995f8161fe5aef245c1496ea4af16dd66981f` |
| `lean/InfoGeometry/Canonical/RealDiracLinearLift.lean` | `3edb4321bf185f3b8435fde51cae33dfcd6dd3fb6f41a50c5ff6e2d9472646a7` |
| `lean/InfoGeometry/Canonical/RealDiracSpinCasimir.lean` | `6b8c7251193c7dcbfdab546eca8a7b618c2984996527a645519e57336cbc5c84` |
| `lean/InfoGeometry/Canonical/RealDiracNambuChecks.lean` | `b637d76add314a179c7cd95c1861e72a84b33d2c21577ee6e7db448686d69f38` |

The published LinearLift after the explicit scalar-evaluation repair has SHA-256
`7766a1206bef596433ab8d39030776d64c14398243f73f19f0065b03316c39e4`.
The other three recovered sources retain the table's hashes.

The adopted parent kernel before the two helper additions has SHA-256
`70383e790bcfc18b700b7ec7096b330cd84526cefb55d42519fa07e94083b6b8`.
It is not the lost base kernel with hash `585f3d34…`.

## Verification and disposition

Use `python3 verification/real-dirac-spin-nambu/check.py --repo . --output <new-report-directory>`
for the focused locked build, fresh file checks, and axiom audit. It reuses the existing
`verification/real-matrix-split` package and its root-matching dependency pins.
No toolchain or dependency change is included.

The new packet had no observed successful compilation before recovery. A queued
build from the prior runtime has no recoverable completion result. Earlier
core/phase acceptance reports do not validate this packet or this different
base. Publication is a draft for review; mathematical acceptance requires fresh
successful compilation, axiom checks, and the applicable repository gates.

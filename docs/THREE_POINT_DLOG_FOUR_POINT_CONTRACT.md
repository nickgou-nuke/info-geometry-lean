# Three-point logarithmic forms and four-point potential: theorem contract

## Provenance and publication status

- Intake date: 2026-11-26 (Europe/Sofia).
- Initial text: `three points in complex plain de rahm cohomology dZ Z potential`
- Refined text: `three points in complex plain de rahm cohomology dZ/Z potential pluker coordinates a way to calculate feynman diagrams`
- Implementation request: implement in the current codebase and publish upstream.
- Base revision: `fe24e350b08fdea04f74c0748ef9fd9417c47529` in `nickgou-nuke/info-geometry-lean`.
- Original local implementation commit: `2201bc74dc7c169853c8f9b545d4a8cf0fec3aff`.
- On 2026-11-27 the user renewed the publication instruction after being told that compiler validation and the repository publication gate were blocked. This authorizes draft publication with those blockers disclosed; it does not turn the pending checks into successful checks.

The earlier execution workspace and its queued compiler sessions were unavailable on resumption. All three Lean sources were recovered from the retained source text and verified byte-for-byte against their previously recorded SHA-256 hashes. The publication commit is recreated against the same upstream base; this document updates the validation/publication record. No successful Lean compilation or transitive kernel axiom audit is claimed.

The mathematical reading is logarithmic differentials on configurations of distinct points, their determinant-coordinate identities, and a concrete four-point logarithmic potential. Three fixed punctures, three moving points, and three points modulo projective transformations are different spaces. A fourth moving/projective point supplies a nontrivial cross-ratio. No equivalence of these spaces is inferred from common notation.

## Existing source owners

| Owner | Reusable content and exact boundary |
| --- | --- |
| `Projective/Quadrics/PluckerKlein.lean` | `pluckerCoord` and `plucker_klein_relation`: finite determinant-coordinate identities. They do not construct a moduli-space quotient. |
| `Projective/CrossRatio.lean` | The existing rational affine cross-ratio convention. The new homogeneous ratio proves compatibility with it. |
| `Projective/AmplituhedronBostConnesSynthesis.lean` | `arnold_rational_field_syzygy`: the reciprocal-difference Arnold identity over a field. The new module consumes this theorem, not the separate socket or certificate structures. |
| `Canonical/IndexedArnoldKZComplex.lean` | Injective configurations, logarithmic coefficients, and finite Arnold/KZ cancellation. Source-inspected context, not a new analytic comparison theorem. |
| `Projective/Conf3ConcreteDLog.lean` | Existing linear-difference Arnold identities. Its separate quadratic-separation coefficients have a counterexample with cyclic sum `3 / 2` and must not be substituted into the linear identity. |
| `Projective/PuncturedAffineLogDeRhamBridge.lean` | Existing constructive cohomology for the one-puncture Laurent complex with differential `T ∂_T`, including the nonzero logarithmic class. This owner is source-inspected, outside the new audit's selected owners. |
| `Feynman/FeynmanTwistedDeRhamComplex.lean` | Exterior multiplication by a supplied square-zero twist. It does not define the full variable-form differential `d + ω ∧` or prove a Feynman-period theorem. |
| `Canonical/BCFWMeromorphicResidueRecursion.lean` | Finite rational identities whose coefficients are not defined as analytic residues. |
| `Twistor/WittenParkeTaylor.lean` | Spinor-bracket rational expressions, distinct from the puncture factor used here. No physical amplitude equality is imported. |

These paths are relative to `lean/InfoGeometry/`. The selected new modules import only four existing project owners transitively: `FiniteSpinAlgebra`, `AmplituhedronBostConnesSynthesis`, `CrossRatio`, and `Quadrics.PluckerKlein`. This avoids the unrelated large dependency chain through `Conf3ConcreteDLog` while preserving direct reuse of an existing Arnold theorem.

## Integrated mathematical owners

### `Projective/ThreePointLogarithmicForms.lean`

The algebra works over an arbitrary field, including the reals and complexes. It constructs native Mathlib `LinearMap` covectors and `AlternatingMap` two-forms.

1. The edge covector is `ω_ij = (z_i - z_j)⁻¹ • (dz_i - dz_j)` on `Fin 3 → K`.
2. The wedge is the genuine alternating bilinear map `(v,w) ↦ a(v)b(w)-a(w)b(v)`.
3. The native Arnold relation is proved by factoring its common numerator and invoking `arnold_rational_field_syzygy`:
   `ω_01 ∧ ω_12 + ω_12 ∧ ω_20 + ω_20 ∧ ω_01 = 0`.
4. The homogeneous coordinate is `u = p01 * p23 / (p02 * p13)`. On the regular chart, the Plücker relation gives `1-u = p03 * p12 / (p02 * p13)`.
5. Affine columns agree with the existing affine cross-ratio. The columns `(0,z,1,∞)`, represented by rows `![0,z,1,1]` and `![1,1,1,0]`, give `u=z`.
6. The logarithmic derivative identities use native `logDeriv`, `HasDerivAt`, and `DifferentiableAt` over a nontrivially normed field.

These are finite covector, alternating-map, projective-coordinate, and ordinary derivative statements. They do not construct a configuration manifold, its exterior derivative, a cohomology-ring comparison, or a Möbius quotient.

### `Feynman/FourPointLogarithmicPotential.lean`

The rational definitions and stationary-point identities work over any field. The Hessian derivative works over any nontrivially normed field. Set

\[
E_{s,t}(z)=\frac{s}{z}-\frac{t}{1-z},\qquad
H_{s,t}(z)=-\frac{s}{z^2}-\frac{t}{(1-z)^2},\qquad
PT(z)=\frac{1}{z(1-z)}.
\]

On the punctured affine domain `z ≠ 0 ∧ z ≠ 1`, and under `s ≠ 0`, `t ≠ 0`, and `s+t ≠ 0`, the source contains proofs of:

- The unique regular solution `z* = s/(s+t)` and the equivalence `E(z)=0 ↔ z=z*`.
- The actual derivative `E'(z)=H(z)`.
- `H(z*) = -(s+t)^3/(s*t)` and its nonvanishing.
- The oriented algebraic readout `-PT(z*)^2/H(z*) = 1/s + 1/t`.
- The same readout from any regular solution, and compatibility with the normalized homogeneous Plücker coordinate.

The minus sign belongs explicitly to `algebraicLocalization`. The unnegated quotient has the opposite sign. This is an algebraic value until a separate analytic residue/integration representation is constructed.

The real potential is

\[
W_{s,t}(z)=s\log|z|+t\log|1-z|.
\]

Mathlib's `Real.log` agrees with the log-absolute convention. The native `HasDerivAt` theorem retains both puncture exclusions, and the stationary-point theorem has derivative zero at `z*`.

The complex expression is `s * Complex.log z + t * Complex.log (1-z)`. Its derivative theorem requires both `z ∈ Complex.slitPlane` and `1-z ∈ Complex.slitPlane`. It is a local principal-branch statement, not a global holomorphic primitive on the twice-punctured plane.

### `Feynman/FourPointLogarithmicPotentialAudit.lean`

The two mathematical owners contain 36 explicit theorem declarations and 12 definitions. The audit selects all their declarations by actual module ownership, including generated/private declarations. It rejects introduced axioms, unsafe or partial definitions, empty owner selections, and transitive axiom dependencies beyond `propext`, `Classical.choice`, and `Quot.sound`.

Nine concrete witnesses cover regular uniqueness, real and complex differentiation at `2/5`, the values `PT=25/6`, `H=-125/6`, and localization `5/6` for `s=2,t=3`, and the three nonzero Arnold summands `1,-1/2,-1/2`. The entire file must exit successfully before its audit is accepted. The source of an audit is not evidence that the audit ran.

## Hypotheses and remaining obligations

- Lean division is total. Zero denominators do not represent geometric poles or admissible chart points.
- If `s=0` and `t≠0`, the candidate stationary coordinate is the excluded puncture `0`.
- If `s+t=0` and `s≠0`, the source proves no finite regular solution exists.
- If `s=t=0`, the equation vanishes identically; uniqueness is not asserted.
- The conditions `s,t,s+t≠0` express algebraic regularity. They are not local-system nonresonance conditions. A sufficient puncture nonresonance condition for complex weights is `s,t,s+t ∉ ℤ`.

Open interpretation and analytic obligations remain:

1. Construct the full `d + ω ∧` differential on variable forms and prove flatness using the actual exterior derivative.
2. Construct the appropriate twisted/relative cohomology and prove any logarithmic-representative comparison.
3. Supply integration cycles and boundary behavior for integration-by-parts identities.
4. Identify the analytic residue or contour integral, including orientation and normalization.
5. For general scattering equations, construct symmetric kinematic weights, prove the row-sum law and Möbius covariance, and separately construct any momentum carrier and pairing.
6. Prove a CHY or physical-amplitude representation theorem with its measure and numerator factors.
7. Construct graph/Symanzik polynomials, their periods, and master-integral reductions before claiming a general Feynman calculation engine.

## Observed validation on 2026-11-26

The two mathematical candidates were generated separately, independently reviewed by a third worker, and integrated by the parent. The parent authored the separate QA module. Independent source review passed for the signs, domains, native carriers, and direct theorem reuse. It is not kernel verification.

| Check | Observed result |
| --- | --- |
| `git diff --cached --check` | Passed. |
| Actual pre-commit hook / `python3 tools/quality/proof_proxy_staged_gate.py` | Passed on the local implementation commit. |
| `tools/infra/axiom_audit.py --fail-on-gaps` on the three Lean files | Passed: zero explicit proof holes or custom axiom declarations. This is a lexical scan. |
| `tools/quality/semantic_vacuity_gate.py --fail-on error` on the three Lean files | Passed at the error threshold; six reviewed warning-level short-proof findings. |
| `tools/quality/semantic_content_audit.py --gate` scoped to the two mathematical owners | Passed: zero findings. |
| `tools/quality/repo_lean_scope_audit.py --fail-on authoritative` scoped to the two mathematical owners | Passed: zero debt findings. |
| `python3 tools/infra/ci_bootstrap.py paths --root .` | Failed: missing/untracked HomotopyHypothesis and Atlas paths, and an uninitialized GIFT gitlink. |
| Lean compilation / transitive axiom audit | No successful result observed. Commands were queued behind another task's exclusive build lock; those sessions were unavailable on resumption. |
| Root publication gate | Not certified; draft publication is an explicit user-authorized exception. |

The six vacuity warnings identify the zero-weight equation, affine and normalized cross-ratio computations, and application equations for `coordinateCovector`, `edgeForm`, and `wedge`. These are computation/evaluation lemmas, not claims of de Rham or physical representation results.

The previously requested compiler commands were:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Projective.Quadrics.PluckerKlein
python3 verification/clifford-peirce-walsh/check.py build InfoGeometry.Feynman.FourPointLogarithmicPotentialAudit
```

The focused checker uses the actual canonical source, the shared build lock, and root-matching dependency pins. It does not certify unrelated root-package dependencies or default targets. The recorded environment is Lean `v4.34.1` with Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## Dependency and publication blockers

The missing HomotopyHypothesis and Atlas paths already occur at the base revision. A bounded search of tracked text and the two known local checkouts found no reconstructible immutable Homotopy revision or tracked Atlas package pin. Atlas's external index says `latest (main)`; a historical inventory records only `34ffed3`. The maintained path preflight rejects upstream-branch or stub substitution.

The recorded GIFT restoration command, `git submodule update --init -- external_refs/gift-framework-core`, exited 128 because upstream did not provide pinned commit `e6f3c3ac2140c2324fb2ae029c32233e73aa5e92` (`upload-pack: not our ref`). The failed task-owned initialization was returned to its original uninitialized state, preserving downloaded Git objects.

No dependency pin, root Lake configuration, toolchain, or quality gate is changed by this patch. Draft publication does not assert that these blockers are resolved or that the source has compiled.

## Source recovery verification on 2026-11-27

| Lean file | SHA-256 matching the prior local implementation |
| --- | --- |
| `ThreePointLogarithmicForms.lean` | `cea95f0cbb4b8c0956afc7331c54e8e545a2dfd0b064c00fc1adea4c2baca0ab` |
| `FourPointLogarithmicPotential.lean` | `091844f58c94afb512a80dea18e4bbff442f5d5c9900731eb7f72290c02ef226` |
| `FourPointLogarithmicPotentialAudit.lean` | `56c351d5e2d47ceb870a43d3d6fab656af707b85825f31128eb1579e79d8f844` |

All three hashes were recomputed from the recovered UTF-8 files and matched. This establishes source identity, not theorem elaboration. The appropriate eventual acceptance scope is native finite logarithmic-form algebra and the stated real/complex four-point calculus; the broader de Rham/CHY/Feynman interpretation remains explicit open debt.

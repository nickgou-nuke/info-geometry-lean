# Graded Clifford modules and the algebraic ABS symbol

## Source and intended claim

Source: M. F. Atiyah, R. Bott, and A. Shapiro, *Clifford Modules* (1964),
the supplied 36-page scan. Printed page numbers are PDF page numbers plus two.
Scan SHA256: `7a3f556b6e9d7dc5e5208d4aff5deabff32ed15da0381edee694534228bb3b40`.

The central source passage is §11, printed page 25 / PDF page 23:
multiplication by `-v` maps the odd module component to the even component;
on the negative unit sphere its inverse is multiplication by `v`.

This task implements that algebraic symbol using the repository's existing
real graded operator representation and native Mathlib Clifford algebras.
It also closes the general grading-compatibility implication required to turn
that representation into an actual object of the existing graded module category.

The representation contract has three explicit inputs:

1. An algebra representation `ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℝ W`.
2. A real linear grading `Γ` with `Γ * Γ = 1`.
3. Generator oddness `Γ * ρ (ι Q v) + ρ (ι Q v) * Γ = 0` for every `v`.

The representation, grading, and generator law are model inputs. Full Clifford
covariance, the real grading decomposition, the symbol maps, and both inverse
identities are derived. Faithfulness and finite-dimensionality are not required
for the linear equivalence. The finite-dimension corollary states
`[FiniteDimensional ℝ W]` explicitly.

## Dependency order and native owners

| Step | Exact construction or implication | Owner / API |
|---|---|---|
| Clifford multiplication | `ι Q v * ι Q v = algebraMap _ _ (Q v)` | Mathlib `CliffordAlgebra.ι_sq_scalar`, `comp_ι_sq_scalar` |
| Clifford parity | Grade involution sends each vector to its negative | Mathlib `involute`, `involute_ι`, `evenOdd` |
| Full represented grading | `Γ * ρ a = ρ (involute a) * Γ`, for every Clifford element | `GradedCliffordOperatorRepresentation.grading_intertwines` |
| Noncommuting real operators | For every real `Q` and `v ≠ 0`, the regular grading does not commute with left multiplication by `ι Q v` | `regular_grading_noncommutes_generator`; closed `negativeLine_grading_noncommutes_generator` |
| Graded module object | Original carrier `W`, represented action, proved semilinear grading | `GradedCliffordOperatorRepresentation.toGradedModule`; existing `GradedMatrixMorita.GradedModuleCat` |
| Real components | `W⁺ = Γ.eigenspace 1`, `W⁻ = Γ.eigenspace (-1)` | `AtiyahBottShapiroSymbol.evenSpace`, `oddSpace` |
| Actual decomposition | `IsCompl W⁺ W⁻` and `W ≃ₗ[ℝ] W⁺ × W⁻` | `isCompl_evenSpace_oddSpace`, `gradingDecomposition`; native `Submodule.prodEquivOfIsCompl` |
| Odd multiplication | `ρ (ι Q v)` exchanges `W⁻` and `W⁺` | `generator_mem_evenSpace`, `generator_mem_oddSpace` |
| Symbol equivalence | `-ρ (ι Q v) : W⁻ ≃ₗ[ℝ] W⁺`, assuming `Q v ≠ 0` | `symbolEquiv` |
| Unit-sphere inverse | If `Q v = -1`, the inverse is `+ρ (ι Q v)` | `symbolEquiv_symm_apply_of_neg_one` |
| Dimension consequence | Equal finite even and odd dimensions when a non-null vector exists | `finrank_oddSpace_eq_evenSpace` |
| Concrete real instance | Native regular representation of the negative real line | `AtiyahBottShapiroSymbolExamples` |

The full covariance theorem uses native Clifford induction: scalars commute
with real linear endomorphisms, the generator case uses the stated oddness
law, and sums and products preserve covariance. No commutativity is imposed
on the represented endomorphism algebra. The regular representation is proved
faithful using `Algebra.lmul_injective`.

The real regular representation also gives an explicit noncommutation theorem.
Commutation of the grading with left multiplication by `ι Q v`, evaluated at
the algebra unit, would imply `-ι Q v = ι Q v`. Cancellation of the real scalar
two gives `ι Q v = 0`; the native linear equivalence with the exterior algebra
then implies `v = 0`. This uses the linear equivalence only as a linear map,
without asserting multiplicativity. The closed `negativeLine` instance at
`v = 1` supplies an actual pair of noncommuting endomorphisms. The one-generator
Clifford algebra itself is not claimed to be noncommutative.

Over the reals, complementary eigenspaces follow from the explicit half-sum
and half-difference decomposition

\[
w=\tfrac12(w+\Gamma w)+\tfrac12(w-\Gamma w).
\]

The equivalence itself reuses Mathlib's complement-to-product construction.
The existing arbitrary-ring graded category uses an additive semilinear
involution; the real decomposition is proved separately, where division by two
is valid.

## Exact sign and signature conventions

Write `c(v) = ρ (ι Q v)`. The native relation gives `c(v)² = Q(v) I`.
For `Q(v) ≠ 0`, the implemented maps are

\[
\sigma_v=-c(v):W^-\longrightarrow W^+,
\qquad
\sigma_v^{-1}=-Q(v)^{-1}c(v):W^+\longrightarrow W^-.
\]

Both compositions are `Q(v)⁻¹ c(v)² = I`. On the paper's negative unit
sphere, `Q(v) = -1`, so the inverse is `+c(v)`.

ABS §2, printed page 6 / PDF page 4, uses
`Q_k(x) = -∑ᵢ xᵢ²`. In the convention where `Cl(p,q)` has `p` positive and
`q` negative squares, these are `Cl(0,k)` algebras. No external complex scalar
or scalar `i` is introduced in the new symbol development.

For an anisotropic form, `v ≠ 0` implies `Q(v) ≠ 0`; the named specialization
`symbolEquivOfAnisotropic` proves this implication before constructing the
equivalence. For an indefinite or degenerate form, a nonzero vector may be null.

One must also distinguish the full operator from a single off-diagonal block.
If `Q(v)=0`, the full Clifford operator is square-zero. That alone does not
show that a particular map `W⁻ → W⁺` fails to be invertible: one off-diagonal
block may be an isomorphism while the other is zero. The present theorem makes
only the sufficient non-null claim and does not assert that this hypothesis is
necessary for an individual chiral block.

## Existing repository content reused and preserved

The structure `GradedCliffordOperatorRepresentation` and its two existing
methods originally belonged to `Canonical/PinOperatorFamilyBridge.lean`.
They are extracted to the focused
`Canonical/GradedCliffordOperatorRepresentation.lean` owner. Their namespace,
field types, and original proofs are preserved. The former owner imports the
new owner, so its concrete `cl11GradedOperatorRepresentation` uses the same
public declarations.

This is a general reusable covariance bridge. Existing representation-specific
covariance results in the Cl(1,1), matrix-tower, chirality, and Fock owners are
not replaced or claimed as new.

`Clifford/KahlerHestenesJWABSPrimary.lean` already supplies substantial ABS
infrastructure: negative and positive forms, the negative-generator inclusion,
grade compatibility, a true graded tensor suspension, actual graded module
categories, and restriction functors. The new constructor reaches that existing
category interface through `Module.compHom`; it does not define a parallel
category.

The existing native `CliffordAlgebra.prodEquiv` is the graded tensor product
equivalence, with its Koszul signs. Native `CliffordAlgebra.equivEven` and the
repository's `FreedCliffordSuspension` handle the even-subalgebra suspension.
These are distinct from the ordinary odd-generator inclusion used for module
restriction, and none is reimplemented here.

The existing general `Physics/ChiralEigenspaceEquivalence` transports eigenspaces
by an operator squaring to `+1`. The ABS symbol needs a different inverse when
`c(v)²=Q(v)I`, particularly for `Q(v)=-1`. Its parity-membership conclusion is
specialized directly from the new representation covariance, avoiding a
dependency on that owner's finite-spin matrix development.

## Scope that remains outside this development

This work constructs a fiberwise algebraic symbol and its real grading spaces.
It does not construct continuity in `v`, a vector bundle map, a relative KO
class, a Spin Thom class, or an index theorem. No inner product or compatible
adjoint is part of the hypotheses, so skew-adjointness is not asserted.

The paper's larger dependency chain still has separate obligations:

- Identify the Grothendieck group of finite graded Clifford modules and the
  map induced by restriction from an additional negative generator.
- Construct the relative bundle class of the symbol and prove that extension
  by an extra generator kills that class.
- Prove multiplicativity and define the comparison map to KO.
- Prove the comparison isomorphism and the Spin Thom theorem with their
  topological hypotheses.

The repository's concrete quotient of the Grothendieck groups of the dimension
monoids `ℕ × ℕ` and `ℕ` is a proved rank calculation. It does not by itself
identify module isomorphism classes with that rank model. Similarly, split
`Cl(n,n)` matrix steps and eight-entry classification tables do not establish
the definite real classification or topological Bott periodicity.

## Validation and review record

Independent mathematical/source review: **PASS**. Independent final QA:
**ACCEPTED_WITH_LIMITED_SCOPE**. The accepted scope is the three new owners and
all four repository modules in their exact source closure, every target-owned
declaration, and source review of the legacy extraction and this document.

Authoring was performed by root and the isolated candidate author. The
independent A-A reviewer was `repo_noether_audit`; the independent QA-A reviewer
was `paper_analysis`. Neither reviewer authored the accepted proof sources.
The original representation structure and both original theorem bodies were
preserved byte-for-byte, with their namespace, binder context, and public names.
The legacy edit consists only of removing that block and importing its new owner.

### Independent native verification

Lean: `4.34.1`, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`.
Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The repository toolchain and dependency pins were unchanged.

| Repository module | Fresh compile exit | Warnings | Owned declarations audited |
|---|---:|---:|---:|
| `OperatorAlgebra.GradedMatrixMorita` | 0 | 0 | Existing dependency |
| `Canonical.GradedCliffordOperatorRepresentation` | 0 | 0 | 50 |
| `Canonical.AtiyahBottShapiroSymbol` | 0 | 0 | 42 |
| `Canonical.AtiyahBottShapiroSymbolExamples` | 0 | 0 | 27 |

All four repository modules were compiled afresh in an isolated output tree.
No repository-module build artifacts were reused in the independent QA run.
The 119 audited declarations include generated declarations and the moved
public declarations under their original namespace. The exact axiom union was
`propext`, `Classical.choice`, and `Quot.sound`; no custom axiom or proof escape
was accepted. These are native foundational dependencies of propositions,
classical constructions, and quotients, not additional ABS assumptions.

The exact independent command, without `--incremental` or `--skip-audit`, was:

```bash
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /workspace/scratch/012eca46cbbe/tmp/mathlib \
  --lean /home/agent/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  --output /workspace/scratch/9401d24a3608/abs-qa-verification \
  --target InfoGeometry.Canonical.GradedCliffordOperatorRepresentation \
  --target InfoGeometry.Canonical.AtiyahBottShapiroSymbol \
  --target InfoGeometry.Canonical.AtiyahBottShapiroSymbolExamples
```

The checker copies the exact source closure, enforces the shared build lock,
checks the pinned compiler and Mathlib source, audits all declarations by owning
module, and rechecks source and checker hashes. QA additionally enforced zero
warnings for all four modules, rather than relying on the checker's original
Clifford-Dirac-specific warning policy. Copied source, live source, staged blobs,
compiled artifacts, and recorded evidence hashes reconciled successfully.

An initially missing compiled `Mathlib.RingTheory.Morita.Matrix` dependency was
recovered by the targeted pinned-Mathlib cache command
`lake exe cache get Mathlib/RingTheory/Morita/Matrix.lean`, under the same shared
lock. It retrieved four missing cache files; existing artifacts and dependency
pins were preserved.

### Static checks and explicit warning dispositions

In the following table, “new owners” means the three target files listed above;
“all changed Lean files” additionally includes `PinOperatorFamilyBridge.lean`.

| Check | Scope | Raw exit | Result |
|---|---|---:|---|
| `opengauss_screener.py --strict --json` | New owners | 0 | No findings |
| `opengauss_cli.py refute --strict --json` | New owners | 0 | Pass |
| `opengauss_cli.py review --gate GATE_4 --json` | New owners | 0 | Static-only pass; native evidence is separate |
| `proof_proxy_staged_gate.py` | Staged changes | 0 | Pass |
| `semantic_vacuity_gate.py --fail-on warning` | New owners | 1 | 16 individually reviewed warnings; raw failure retained |
| `opengauss_screener.py --strict --json` | All changed Lean files | 1 | Exactly two unchanged legacy warnings; raw failure retained |
| `git diff --check` and `git diff --cached --check` | Working and staged changes | 0 | Pass |

The semantic scanner's 16 warnings are 13 elementary membership/evaluation or
constructor API lemmas, two original defining fields, and one alias reusing the
closed negative-line model. QA inspected each flagged declaration and recorded
its mathematical role. The input fields are proved in the regular and closed
negative-line models. Full covariance, complementarity, and both symbol inverse
identities are separate proved results. The raw warning-fail result is not
reported as a clean automated pass.

The two full-changed-file warnings are the pre-existing unused `hG` hypotheses
in `pinGrading_morita_unit_compatibility` and
`pinGrading_morita_counit_compatibility`. Their declarations and proofs are
unchanged from baseline `fe24e350b08fdea04f74c0748ef9fd9417c47529`.

The independent acceptance record is `abs-qa-verification/qa-acceptance.json`,
SHA256 `f8b8677b0ffba90c28cc0bb01704e107b691846d63bc0f5b87b6a3f35eb422a3`.
Its evidence manifest is `abs-qa-verification/qa-evidence-sha256.json`,
SHA256 `11661512fb6891ea18f875a737a57bf4b34a9f66418d67c31c5619f78b1d31da`.
These hashes identify observed evidence; they are not substitutes for the
native proofs or claims of immutable storage.

### Build coverage limit

The ordinary root Lake environment has missing configured path packages,
including `external_refs/homotopy-hypothesis-lean4` and
`external_refs/atlas-lean`. The focused checker used the unchanged pinned
Mathlib checkout and exact repository source closure. The independent QA run
did not compile the entire heavy legacy Pin import graph or run a broader root
Lake build. The legacy extraction has source/API preservation evidence, and
this acceptance is not a whole-repository build certificate.

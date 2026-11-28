# Arnold–Klein operator symmetry: theorem contract

## Intake and source authority

User intake, preserved verbatim:

> arnnold sdiff grouop lifted to a symmetry closure grouop for abstract vector fileds lets thenink abut the connections and mappps between the symmetries of the flow vector fileds and geometry felix klein

Implementation authorization, preserved verbatim:

> implement and publish on upstream

The immediately preceding mathematical proposal separated real derivations,
generated flows, conjugation, invariant–stabilizer closure, real cotangent lifts,
momentum maps, and orbit/stabilizer geometry. This contract implements the
operator portion of that proposal on existing native carriers. Historical
connections to Arnold and Klein are motivation; every promoted assertion must
be represented by an explicit map and theorem below.

Initial implementation base: `fe24e350b08fdea04f74c0748ef9fd9417c47529`.
A fresh remote read identified current upstream `main` at
`e2aa23c786c63c8992e8936346ed5f7782e4e164`; the patch is integrated into an
independent checkout of that revision on branch
`codex/arnold-klein-operator-closure-20261128`. Five of the six imported
repository dependencies are byte-identical between these revisions. The sixth,
`Meta/Architecture`, adds metadata and explicit audit commands while retaining
the interfaces used here; the fresh validation compiled that changed dependency.
Smooth SDiff constructions are not assumed dependencies of this operator model.

## Carriers, conventions, and existing owners

- `InfoGeometry.Algebra.NonAssocDerivation.derivations R A` is the existing
  native `LieSubalgebra R (Module.End R A)` of Leibniz endomorphisms. Preserve
  noncommutative multiplication. Native algebra equivalences provide the
  associative specialization of multiplication-preserving linear transport.
- `LinearEquiv.lieConj` supplies conjugation on the endomorphism Lie algebra.
- `InfoGeometry.Lie.ContinuousDerivationExponential.flow` is the existing
  bounded real exponential flow. Analytic theorems retain completeness and
  continuous linear/bilinear maps; arbitrary unbounded generators are excluded.
- `InfoGeometry.Clifford.NeutralPhaseSpaceCore.PhaseSpaceCarrier E` is
  `E × Module.Dual ℝ E`. Reuse its `canonicalNeutralBilin`, `neutralOmega`, and
  `neutralParaInvolution`. The alternating convention is
  `Ω((v,λ),(w,η)) = η(v) - λ(w)`; the symmetric convention is the unscaled sum.
- `InfoGeometry.Canonical.SouriauContragredientPairing` owns the inverse-dual
  linear equivalence and its evaluation compatibility.
- Native `fixingSubgroup_fixedPoints_gc`, `ClosureOperator`, `Subgroup.closure`,
  `MulAction.stabilizer`, and `MulAction.orbitEquivQuotientStabilizer` supply
  the group/action layer. A normalizer, a generated subgroup, and a
  topological closure are distinct constructions.

## Verified claim ledger and proof dependencies

| ID | Exact target | Hypotheses / boundary | Verification |
| --- | --- | --- | --- |
| D1 | Multiplication-preserving conjugation preserves the Leibniz rule and restricts to a Lie equivalence of the existing derivations | Commutative scalar ring `R`; associative ring `A` with `Algebra R A`; an algebra automorphism | `[kernel_verified]` |
| D2 | Derivations annihilated by a linear functional form a Lie subalgebra; invariant functional data survive conjugation | `ω ∘ D = 0`; exact invariance of `ω` under the equivalence | `[kernel_verified]` |
| D3 | The Lie span of the conjugates of a generator family is invariant under the generating action | Group of algebra automorphisms; conjugation-saturated family | `[kernel_verified]` |
| F1 | A continuous functional is invariant under every real time of the exponential flow exactly when it annihilates the bounded generator | Complete real normed carrier; bounded generator and functional | `[kernel_verified]` |
| C1 | Generated flow transformations embed into their invariant–stabilizer closure; this closure has the same chosen fixed data | Explicit ambient group/action and chosen invariant carrier | `[kernel_verified]` |
| C2 | The bounded-flow group and its chosen functional symmetry closure preserve an annihilating functional | F1 and the chosen dual action; no trace assumption | `[kernel_verified]` |
| C3 | The actual symmetry closure has a faithful primal/dual representation preserving both native forms and the grading, compatible with the original flows | C1, native subgroup inclusion, and L1 | `[kernel_verified]` |
| L1 | The inverse-dual lift on the existing primal/dual carrier is multiplicative and injective, and preserves both native forms and the grading | Real modules and native linear equivalences | `[kernel_verified]` |
| L2 | `D ↦ (D,-D*)` preserves endomorphism commutators and the lifted infinitesimal action preserves both forms | Actual operator composition order; no commutativity assumption on generators | `[kernel_verified]` |
| H1 | `H_D(v,λ)=λ(Dv)` satisfies the explicit bilinear Hamiltonian differential identity | Algebraic directional polarization; differentiate analytically only under stated topological hypotheses | `[kernel_verified]` |
| H2 | The evaluation momentum map is equivariant under inverse-dual lift and conjugation | Algebraic dual of the full real endomorphism algebra; the full real linear-equivalence group | `[kernel_verified]` |
| O1 | Equivariance yields stabilizer containment and the induced map between state and momentum orbits | The stated phase-space and momentum actions of the full real linear-equivalence group; set-level quotient | `[kernel_verified]` |

The causal order is D1→D3, D2/F1→C2, C1/L1→C3, and L1/L2→H1/H2→O1.
C1 is independent native group/action infrastructure. No edge is inferred from
historical naming.

## Implemented maps

The four canonical owners below passed the native selected-source check and
declaration audit. The exact verification scope and source binding are recorded
below.

| Owner | Main map or theorem | Mathematical content |
| --- | --- | --- |
| [DerivationSymmetry](../lean/InfoGeometry/Algebra/DerivationSymmetry.lean) | `conjugateDerivation`, `annihilatingDerivations`, `map_conjugationLieSpan` | Algebra automorphisms act on actual Leibniz endomorphisms; functional annihilators and conjugation-saturated Lie spans are preserved. |
| [ContinuousDerivationInvariantFunctional](../lean/InfoGeometry/Lie/ContinuousDerivationInvariantFunctional.lean) | `functional_flow_invariant_iff` | A continuous functional is invariant at every real time exactly when it annihilates the bounded generator. |
| [NeutralPhaseSpaceSymmetry](../lean/InfoGeometry/Clifford/NeutralPhaseSpaceSymmetry.lean) | `dualLiftHom`, `infinitesimalLiftLieHom`, `momentumEquivariant`, `momentumQuotientMap` | Faithful real primal/dual transport, ordered commutators, Hamiltonian evaluation, and maps from state orbits to momentum orbits. |
| [OperatorFlowClosure](../lean/InfoGeometry/Erlangen/OperatorFlowClosure.lean) | `flowAlgEquiv`, `flowGroup`, `flowSymmetryClosure`, `functional_closure_eq_self`, `closureDualLiftHom` | Bounded derivations generate native algebra automorphisms whose chosen invariant-data closure preserves the same functional and acts faithfully on the primal/dual phase space. |

For a generator family `D i`, the group and its closure are explicitly

\[
G_D=\langle\exp(tD_i):i\in I,\ t\in\mathbb R\rangle,
\qquad C_T(G_D)=\operatorname{Fix}(\operatorname{FixedPoints}(G_D,T)).
\]

Here `T` includes a specified action of the ambient algebra automorphism group.
Changing this data action can change the closure. The native Galois connection
gives `G_D ≤ C_T(G_D)`, idempotence, and equality of the chosen fixed-data sets.
For the chosen inverse-dual action on `Module.Dual ℝ A`, the functional theorem
feeds into the actual generated group:

\[
(\forall i,\ \omega\circ D_i=0)
\Longrightarrow
\omega(\alpha x)=\omega(x)
\quad(\alpha\in C_{A^*}(G_D)).
\]

The functional Lie-span theorem in `OperatorFlowClosure` applies `DerivationSymmetry`
to this specific group: the Lie span of all closure-conjugates of the original
generators still annihilates `ω`. This is an algebraic conclusion. The closure
may contain discontinuous algebra automorphisms, so their conjugated
derivations are not automatically bounded or integrable.

On the real primal/dual carrier, the maps retain their exact signs:

\[
\ell(U)(v,\lambda)=(Uv,\lambda\circ U^{-1}),\qquad
L_D(v,\lambda)=(Dv,-\lambda\circ D).
\]

`dualLiftHom` is injective, preserves both core bilinear forms, and commutes
with the grading. `closureDualLiftHom` explicitly composes subgroup inclusion,
forgetting multiplication, and this lift:

\[
C_T(G_D)\hookrightarrow\operatorname{Aut}_{\mathbb R\text{-alg}}(A)
\longrightarrow\operatorname{GL}_{\mathbb R}(A)
\xrightarrow{\ell}\operatorname{GL}_{\mathbb R}(A\oplus A^*).
\]

The composite is faithful, preserves both forms, and commutes with the grading.
`closureDualLiftHom_flow` states that including an original time-flow in the
closure and then applying this composite agrees with lifting its existing
linear flow directly. This gives the closure group an explicit representation
on the phase space and a compatibility statement for each original flow.

`infinitesimalLiftLieHom` preserves the endomorphism commutator. The native
quadratic Hamiltonian and its algebraic differential satisfy

\[
H_D(v,\lambda)=\lambda(Dv),\qquad
d_{\mathrm{alg}}H_D(z)[w]=\Omega(L_Dz,w),
\]

with the exact affine-line identity

\[
H_D(z+tw)=H_D(z)+t\,d_{\mathrm{alg}}H_D(z)[w]+t^2H_D(w).
\]

The momentum value `momentum z` is a native linear functional of the generator.
For the native real linear-equivalence group `G = E ≃ₗ[ℝ] E`, equivariance
yields actual surjections

\[
G\!\cdot z\longrightarrow G\!\cdot\mu(z),
\qquad G/G_z\longrightarrow G/G_{\mu(z)}.
\]

The quotient spaces here are native coset sets. No normality, quotient-group
structure, or smooth homogeneous-space structure is assumed.

## Adjacent claims and boundaries

- A group of volume-preserving transformations need not preserve a metric.
- A symmetry closure can add a time-reversing transformation unless the chosen
  invariant signature retains the generator or orientation.
- Endomorphism commutators and fundamental vector-field brackets have opposite
  signs for the left linear-action convention. This work must not identify them
  without the corresponding sign map.
- The set-level orbit/stabilizer equivalence does not construct a smooth
  homogeneous quotient, a Cartan connection, or a Riemannian metric.
- The algebraic and bounded-flow results do not integrate arbitrary Type III
  modular generators or extend an unbounded weight outside its domain.
- An implementation in a chosen representation and a central-extension
  classification require additional theorems. The present map contracts do not
  assume every automorphism is implementable or that its commutant is central.
- Euler–Arnold evolution additionally needs an inertia operator and analytic
  well-posedness. It is not inferred from invariant–stabilizer closure.

## Validation and publication record

Recorded on 2026-11-28. The exact statements in the claim ledger are
`[kernel_verified]`: the native selected-source check and all-declaration audit
both passed. The implemented algebraic and bounded-flow interpretation is
`[accepted_limited_scope]`. The additional smooth SDiff, unbounded-generator,
and Euler–Arnold conclusions described in the boundaries remain
`[bucket_3_open_debt]`.

The full repository publication gate has not passed, and this patch has not
been published. This is a separate acceptance condition from native proof
verification.

### Native selected-source check

The checker uses Lean `4.34.1`, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`, and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The eight transitive Mathlib
package revisions were checked against the root manifest. All nine package
heads, including Mathlib, and their tracked-source cleanliness were checked
again after the successful native run. The selected source closure consists
of the four new owners and six unchanged repository
dependencies. All six dependency source files match upstream
`e2aa23c786c63c8992e8936346ed5f7782e4e164` byte for byte.

Exact command used, from the independent repository checkout:

```bash
python3 tools/quality/check_operator_geometry.py \
  --repo /home/agent/arnold-klein-upstream \
  --mathlib /workspace/scratch/882633407e39/flow-runtime/mathlib \
  --lean /workspace/scratch/882633407e39/flow-runtime/lean-4.34.1-linux/bin/lean \
  --work-dir /home/agent/arnold-klein-validation/native \
  --target InfoGeometry.Algebra.NonAssocDerivation \
  --target InfoGeometry.Algebra.FiniteSpinAlgebra \
  --target InfoGeometry.Lie.ContinuousDerivationExponential \
  --target InfoGeometry.Meta.Architecture \
  --target InfoGeometry.Clifford.NeutralPhaseSpaceCore \
  --target InfoGeometry.Canonical.SouriauContragredientPairing \
  --target InfoGeometry.Lie.ContinuousDerivationInvariantFunctional \
  --target InfoGeometry.Erlangen.OperatorFlowClosure \
  --owner InfoGeometry.Algebra.DerivationSymmetry \
  --owner InfoGeometry.Lie.ContinuousDerivationInvariantFunctional \
  --owner InfoGeometry.Clifford.NeutralPhaseSpaceSymmetry \
  --owner InfoGeometry.Erlangen.OperatorFlowClosure \
  --owner-warnings-as-errors --incremental --audit \
  --audit-source tools/quality/ArnoldKleinOperatorDeclarationAudit.lean
```

The command takes the shared build lock, snapshots the complete selected
source closure, and verifies that sources and verification tools stay
unchanged during the run. Incremental reuse is limited to unchanged checked
dependencies; the strict-owner option recompiles every selected owner with
`warningAsError=true`.

The declaration audit enumerates ownership by actual Lean module identity,
including private and generated declarations. It rejects unsafe and partial
declarations, local axioms, and any transitive axiom outside `propext`,
`Classical.choice`, and `Quot.sound`. The Python checker independently validates
the audit's owner coverage, declaration uniqueness, dependency consistency,
and axiom whitelist. The completed audit reported **PASS for 163 declarations**:
131 theorem declarations and 32 definitions, including generated declarations.
All four requested owners were nonempty and covered. No unsafe or partial
owned declaration, local axiom, or transitive axiom outside the whitelist was
accepted.

The unchanged `ContinuousDerivationExponential` dependency emitted existing
deprecation and unused-section-variable warnings when compiled. The strict
warning requirement applies to the four new owners; the entire imported
closure is not described as warning-free.

### Exact source binding

The successful snapshot contains the exact proof-source bytes committed in
`8d7fefd67d235677e725901819899a09994b4458`. Every one of its ten module hashes
was independently compared with that commit's Git blobs and the current
working files; all matched. The verification-tool hashes also matched.

The snapshot metadata recorded the preceding HEAD,
`a45602acca18516a8c7084c21fe098996d228863`, because the time-zero functional
proof repair was staged when the snapshot was taken and committed while the
run waited for the build lock. The committed source-byte comparison above
establishes the binding to the repaired proof; the preceding HEAD is not
substituted for it.

| Audited module | Declarations | Source SHA-256 |
| --- | ---: | --- |
| `Algebra.DerivationSymmetry` | 39 | `d8a24dee52ba81815a094d239695c1df4e4f8e2594fbf1d89425e14cfae579f2` |
| `Lie.ContinuousDerivationInvariantFunctional` | 4 | `51c23c2db02d388b1b8daaa1d9f9b31833c97c73404e96e8771ea5fb9f2343a6` |
| `Clifford.NeutralPhaseSpaceSymmetry` | 69 | `c6fafc50bf32463c0d8b60ee5301ecff9b16311d81ede4f4ccfe7b965f5b43b6` |
| `Erlangen.OperatorFlowClosure` | 51 | `df500b7a7d87b012b48bc4ddb0b58721e5390a3e89c33e7dac306ef869d3af3b` |

The source hashes, rather than a filename or namespace prefix, identify the
checked content. This documentation update changes none of those proof files.

### Other completed checks

- The scoped source-debt audit passed for all four owners with zero gaps.
- The source-scope audit passed for the four owners and declaration audit.
- The scoped lexical semantic-content audit reported zero findings. This is
  a source scanner, separate from kernel verification and mathematical review.
- The staged proof gate passed after the proof repairs, and the actual tracked
  pre-commit hook passed on both implementation commits.
- `python3 -m unittest discover -s tests/quality -p test_two_boundary_gate_routing.py -v`
  passed all seven tests. The regression suite uses a subprocess recorder to
  verify gate routing; it does not stand in for Lean compilation.

### Maintained root build and publication prerequisites

The actual maintained root owner build was attempted with the same Lean
version:

```bash
PATH="/tmp/arnold-lean-runtime/lean-4.34.1-linux/bin:$PATH" \
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Algebra.DerivationSymmetry \
  InfoGeometry.Lie.ContinuousDerivationInvariantFunctional \
  InfoGeometry.Clifford.NeutralPhaseSpaceSymmetry \
  InfoGeometry.Erlangen.OperatorFlowClosure
```

It exited 1 during package loading, before compiling any owner:

```text
error: Atlas: package directory not found: /home/agent/arnold-klein-upstream/external_refs/atlas-lean
```

Exact pinned Stacks and Homotopy sources were restored. The path-package
provenance preflight still reports unresolved Atlas provenance and the stale
GIFT dependency. No dependency or toolchain revision was changed.

The following checkout preflights were also run:

```bash
python3 integrations/grh/verify_sources.py --lane all --checkouts
python3 integrations/grh/verify_sources.py --lane external --checkouts
```

The first exited 1 because the native GRH lane lacks its independent Mathlib
checkout; the second exited 1 because the external lane lacks its GRH
checkout. These are checkout-preflight failures, not failed GRH theorem
compilations. The full publication gate has not passed.

### Publication state

No remote branch, pull request, or merge has been created for this patch.
The user's ordinary implementation and upstream-publication authorization
remains active. [AGENTS.md](../AGENTS.md) and [RUNBOOK.md](../RUNBOOK.md)
require the maintained staged and push gates and prohibit replacing a required
gate with a narrow check. The new-ref hook applies to draft branches as well.
Publication therefore still requires a working gate environment or an
explicit exception to these repository acceptance requirements. Native
selected-source verification is a separate result from publication acceptance.

# Conformal-balance intake: Peirce criteria and the unitary obstruction

## Intake and disposition

Source: user attachment `Pasted text(9).txt`, 27,400 bytes, SHA-256
`2b57085958c4ebf3de8a0355adecda23fa4a00280723c0cc2c6bd79c86648c05`.
The unchanged attachment is preserved in the task workspace. This record
retains the proposed identifications and distinguishes their mathematical
status rather than silently replacing them with weaker statements.

The branch starts from upstream
`3d7eb6d9b0af5636ab12b3d0b91b82740507e49e`. It is independent of the earlier
nilpotent/colimit and resolvent PRs (#289 and #292).

Disposition: **[kernel_verified]** for the nine new theorem statements,
including independent rebuild and complete declaration audit;
**[accepted_limited_scope]** relative to the larger conformal-net intake.
The exact quartic Peirce word is already owned by the repository.
The proposed additions characterize when that word is trivial or exactly
quadratic, and establish the obstruction to a nontrivial square-zero
unipotent being unitary in a C*-ring. They do not construct a conformal net
or prove the external conformal-net balancing theorem in Lean.

## Checked external references

1. Adrià Marín-Salvador, [The balanced structure on the category of
   representations of a conformal net](https://arxiv.org/html/2605.18446v2),
   arXiv:2605.18446v2; [published version](https://doi.org/10.1063/5.0347959),
   *Journal of Mathematical Physics* 67, 102302, 26 October 2026.
2. Adrià Marín-Salvador, [Twisted representations of conformal nets and crossed
   balanced tensor categories](https://arxiv.org/html/2606.03623v3),
   arXiv:2606.03623v3, 4 August 2026.
3. Fumio Hiai, [Concise lectures on selected topics of von Neumann
   algebras](https://arxiv.org/pdf/2004.02383), arXiv:2004.02383, section 12.2,
   Proposition 12.11, Remark 12.12, and Example 12.15, for the modular
   comparison used below.

The first paper's Theorem 4.4 supplies the canonical balance for the stated
conformal-net category, without rationality. Its Definition 4.1 makes the
balance a **unitary** rotation operator. Section 3.1 constructs Connes fusion
using an inner product and Hilbert completion. The second paper treats a
faithful discrete group action and a crossed twist with typed target `gX`.
These are external mathematical results, not new kernel-checked declarations
in this change. In particular, their Hilbert-space setting is not changed to
an indefinite Krein inner product by dropping rationality.

## Atomic claim ledger

| ID | Intake claim | Status and correction |
|---|---|---|
| C01 | A diffeomorphism-covariant conformal net has the cited canonical balance | External theorem under its definitions; its construction remains outside this Lean addition |
| C02 | DHR representations themselves require rationality or finite index | Overstrong. The existence of a rigid/rational construction of a twist is a different issue from the existence of the DHR category |
| C03 | Vacuum Möbius covariance forces every sector's rotation twist to be the identity | Overstrong. A vacuum group action and a sector's lifted action are different data; the absence of a canonical lift does not prove triviality of every possible lift |
| C04 | Two complementary open semicircles have union equal to the entire circle | Their boundary points are omitted. A geometric interval split is not a Hilbert direct-sum projection |
| C05 | Haag duality is literally the Peirce decomposition `1=P+(1-P)` | No identifying map is supplied. Commutants of interval algebras and corners cut out by an idempotent are different constructions |
| C06 | Connes fusion is the multiplication of the two Peirce unipotent gates | Open bridge. A relative tensor product requires module actions, an inner product, completion, and coherent comparison maps |
| C07 | The Connes cocycle is simply the power of the relative modular operator | Incorrect in general; a reference modular factor is missing. Equality of the two states already distinguishes the two expressions |
| C08 | The balancing law gives `L0(fused)=L0(left)+L0(right)+Omega` | Not a consequence of one rotation identity. The operators, common domains, and generator comparison must first be constructed |
| C09 | The balancing monodromy is `exp(-2*pi*i*Omega)` | Conditional on an actual generator decomposition and appropriate commutation hypotheses. Noncommuting exponentials cannot be split this way |
| C10 | Every conformal Hamiltonian is a scaled quadratic Casimir | Unsupported as a statement about arbitrary conformal nets; no model-specific construction is given |
| C11 | The Casimir cross-term is the Peirce operator `V`, hence a Fisher metric | Open bridge. No intertwining representation, scalar pairing, or metric identification is supplied |
| C12 | Non-rationality admits the proposed nonzero nilpotent Jordan rotation inside the unitary category | Rejected by the unitary square-zero obstruction below, whenever the proposed bounded operator formula applies |
| C13 | For square-zero `N`, the analytic exponential is `1+z*N` | Valid under the native normed-algebra hypotheses; this does not imply the result is unitary |
| C14 | `Gplus-Gminus=Sigma` is always nonzero | The equality is algebraic; nonvanishing needs an additional hypothesis |
| C15 | The four-factor word is exactly `1+Sigma-V*Phi` | False. Its cubic term is `-V*J`, and the quartic term `Qplus^2` is present |
| C16 | The four-factor word is exactly `1+Sigma-V*J+Qplus^2` | Existing owner-backed theorem; reused rather than duplicated |
| C17 | The four-factor word is literally `1+Sigma` | Valid exactly under the new cubic-vanishing criterion; false in general |
| C18 | An operator group commutator is automatically categorical double braiding | Open bridge. The object assignment, tensor structure, braiding maps, and coherence laws must be supplied |
| C19 | The crossed braiding convention fixes the sign of a Peirce chirality operator | No compatibility map between these data is given |
| C20 | A `c/24` modular-character shift follows from the ordinary balance alone | Additional character, central-charge, and modular-action data are required |
| C21 | A general balanced category is automatically a ribbon category | Rigidity and the appropriate compatibility with duals are additional obligations |
| C22 | A square-zero displacement automatically lies on a Krein null cone | An indefinite form and the relevant adjoint relation are required. Nilpotency alone does not imply that the image vector is isotropic |

The paper writes the tensor twist after the double braiding. Moving it
before the double braiding uses naturality of the braiding with respect to
the two component twists. It is not permission to commute arbitrary
operator factors in the Peirce word. Likewise, an `O(degree 3)` expression
needs a declared formal filtration or an analytic estimate; the criteria
formalized below are exact equations and use neither interpretation.

### Two explicit failed identifications

For `P=E11`, `a=E12`, `b=E21` in `Mat_2(Z)`, the genuine noncommuting
Peirce corners give

```text
W = [[3,-1],[1,0]],       1+Sigma = [[2,0],[0,0]],
1+Sigma-V*Phi = [[2,-1],[-1,0]].
```

Here `V=1`, `J=a-b`, and `Qplus^2=E11`. Thus both shortened expressions
fail on the operator carrier, while the existing quartic formula is exact.
This calculation is explanatory evidence; the general criteria below are
the targets of Lean verification.

For the modular claim, take equal faithful states `psi=phi`. Their Connes
cocycle is the identity. The relative modular operator for the equal pair
is the state's modular operator and need not be the identity. In the
finite matrix standard representation on Hilbert-Schmidt operators,
`Delta_phi(X)=rho*X*rho^(-1)`. A nontracial invertible density, for example
`rho=diag(2/3,1/3)`, gives `Delta_phi(E12)=2*E12`. Therefore the cocycle
cannot generally be identified with `Delta_(psi|phi)^(it)` alone. The
standard representation comparison uses the additional reference modular
factor. For faithful normal states in standard form, Hiai's Proposition
12.11 and Remark 12.12 give

```text
(Dpsi:Dphi)_t = Delta_(psi,phi)^(it) * Delta_phi^(-it).
```

His Example 12.15 gives the density-operator expression on `B(H)`.
No modular-theory formalization is claimed here.

## Existing owners and search boundary

Paths in the following table are relative to `lean/InfoGeometry/`.

| Owner | Actual reusable content or limitation |
|---|---|
| `OperatorAlgebra/PeirceSpine/Basic.lean` | Existing Peirce corners, grades, and characteristic-free normalization tactic |
| `OperatorAlgebra/PeirceSpine/Tetraktys.lean` | `tetraktys_interaction_iff_chiral_obstruction`: `V=0` iff `Sigma=0` |
| `OperatorAlgebra/PeirceSpine/WilsonPlaquette.lean` | Existing ordered words, both exact quartic expansions, and the symmetric even-part readout |
| `OperatorAlgebra/PeirceDefectBridge.lean` | `genV_eq_zero_iff_qgt_zero`: `V=0` iff both ordered mixed products vanish |
| `Quantum/QutritMobiusFiniteFlowClassification.lean` | A private generic square-zero exponential proof using the actual analytic exponential; not a public shared API |
| `Canonical/LogJordanKreinCore.lean` | Actual exponential calculation on its specified real 2-by-2 Jordan carrier |
| `Canonical/MonoidalRibbonPentagonHexagonCapstone.lean` | `RibbonTwist.theta_tensor` is an input field. The structure lacks naturality and does not construct a conformal-net balance |
| `Categorical/LogNilpotentMonoidalCategory.lean` | Actual finite nilpotent-module monoidal structure; not Connes fusion |
| `Categorical/LogNilpotentAmbientSymmetric.lean` | The existing ambient swap is a symmetric braiding |
| `Categorical/LogJordanCheckedRBraidBridge.lean` | `standard_logCheckedR_monodromy_eq_id` proves identity for the standard double swap; nontrivial generic checked-R data is an input |
| `OperatorAlgebra/PeirceSpine/TripotentMoritaForwardBimodule.lean` | An algebraic tensor-quotient construction, without the Hilbert completion needed for Connes fusion |

The search covered Lean paths, declarations, alternate words for fusion,
conformal nets, DHR/Haag duality, ribbon balance, monodromy, unipotent
products, and consumers of the relevant owners. No construction establishing
the proposed conformal-net/Peirce equivalence was located. This records that
search result, not a claim that every possible equivalent formulation is
absent.

Native Mathlib `CategoryTheory.Balanced` means that a morphism that is both
monic and epic is an isomorphism. It is unrelated to a braided categorical
twist. Mathlib's `BraidedCategory` supplies typed braidings and hexagon laws;
having that interface does not construct an instance for conformal nets.

## Contract A: exact Peirce criteria

Carrier: an arbitrary associative `B` with `[Ring B]`.
Input: `P : B` with `hP : P * P = P`, and independent `A C : B`.
There is no characteristic, positivity, self-adjointness, or invertibility
assumption on `A` and `C`.

All definitions are reused from the existing owner:

```text
a      = conePlus P A  = P*A*(1-P)
b      = coneMinus P C = (1-P)*C*P
J      = a-b
Sigma  = a*b-b*a
V      = a*b+b*a
Qplus  = a*b
Qminus = b*a
W      = (1+a)*(1+b)*(1-a)*(1-b)
```

The nilpotency of each corner makes `1-a` and `1-b` the actual inverses
of the corresponding factors. It does not kill alternating cubic or
quartic words.

The five new theorems in `PeirceSpine/WilsonPlaquetteCriteria.lean` are:

```text
W = 1         iff Sigma = 0
W = 1         iff V = 0
W = 1         iff Qplus = 0 and Qminus = 0
W = 1+Sigma   iff V*J = 0
W = 1+Sigma   iff a*b*a = 0 and b*a*b = 0
```

For the first criterion, the exact ordered identities

```text
(W-1)*(1+b)*(1+a) = Sigma
W-1 = Sigma*(1-a)*(1-b)
```

cancel the group factors without commuting them. The other triviality
criteria use the existing Peirce zero criteria.

For exact quadratic truncation, the odd projection of `W-(1+Sigma)` is
`-V*J`. If `V*J=0`, then `Qplus^2=P*(V*J)*b=0` as well. Finally, the two
left corner projections of `V*J` give `a*b*a` and `-b*a*b`. These are
actual proof dependencies and are valid in every characteristic.

## Contract B: the C*-unitary obstruction

Algebraic-normed carrier: `[NormedRing B] [StarRing B] [CStarRing B]`.
Input: `N : B` satisfying `N*N=0`.
Native unitarity: membership in `unitary B`.

Main target:

```text
(1+N) in unitary B iff N=0.
```

Its obstruction uses positivity through the C*-identity, not a
finite-dimensional diagonalization. Unitarity identifies `star(1+N)`
with the inverse `1-N`, so `star N=-N`. Therefore `star N*N=0`, and native
`CStarRing.star_mul_self_eq_zero_iff` forces `N=0`.

Left multiplication by an arbitrary already-unitary factor preserves
unitarity. Consequently adding such a phase/factor does not permit a
nonzero square-zero unipotent in the positive Hilbert-space setting.

The analytic corollary additionally uses `[NormedAlgebra ℂ B]` and
`[CompleteSpace B]`, and a
nonzero complex scalar `z`. It concerns the actual `NormedSpace.exp`:

```text
exp(z • N) in unitary B iff N=0.
```

The square-zero series truncation is used in this proof; it is not a
redefinition of the exponential. A nonzero nilpotent may still occur in
an indefinite-star algebra where the C*-hypothesis fails. No theorem here
transfers the positive Hilbert-space balance to that different setting.

The four declarations in `OperatorAlgebra/SquareZeroUnitary.lean`
are `one_add_mem_unitary_iff`, `mul_one_add_mem_unitary_iff`,
`exp_smul_mem_unitary_iff`, and `mul_exp_smul_mem_unitary_iff`.
The latter two use a nonzero `z : ℂ`; the left-factor variants take
`hU : U ∈ unitary B`. No scalar-star compatibility or commutation between
`U` and `N` is required.

## Proven dependency order

| Node | Mathematical input | Depends on |
|---|---|---|
| A1 | Idempotent and complementary corner support | Ring laws and `hP` |
| A2 | Existing nilpotent gate word and quartic expansion | A1, existing Wilson owner |
| A3 | Trivial-word iff criteria | A2, ordered cancellation, existing Peirce zero criteria |
| A4 | Exact quadratic criterion | A2, odd projection and opposite-corner readouts |
| B1 | Star of a square-zero unipotent under unitarity | Star-ring laws, native unitarity, `N*N=0` |
| B2 | Nilpotent part vanishes | B1, C*-definiteness |
| B3 | Unitary-factor and analytic-exponential consequences | B2, native unitary multiplication and convergent exponential |

The two columns of results share operator language but have different
hypotheses. No dependency edge to Connes fusion, a conformal-net category,
a Casimir identification, or a Fisher metric is asserted without a map
and its compatibility theorem.

## Validation record

Compiler: Lean `4.34.1`, commit
`5045d0056413266e57c625dcd7c365b10e377c52`.
Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

| Check | Result and scope |
|---|---|
| Independent mathematical source review | PASS for both new owners and Contracts A/B |
| Fresh selected source-closure compilation | PASS: 24 project modules, comprising two new owners and 22 unchanged dependencies |
| New-owner compiler warnings | Zero; both compiler logs are empty |
| Unchanged dependency diagnostics | Four existing linter warnings in `PeirceSpine.Supercharge`; two informational tactic suggestions in `PeirceSpine.Unipotent` |
| Independent rebuild and complete native declaration audit | PASS: both new owners recompiled afresh; all 20 owned declarations, including generated proof helpers, audited |
| Staged proof-source gate and whitespace check | PASS |
| Ordinary Lake integration | Not yet certified; the pinned GIFT configuration remains a separate integration obligation |

From the repository root, the successful fresh source check was:

```bash
source /workspace/scratch/2e3cbf77ee2a/runtime/environment.sh
python3 tools/quality/check_operator_geometry.py \
  --repo /workspace/scratch/2771a9ff6f38/info-geometry-lean \
  --mathlib /workspace/scratch/2e3cbf77ee2a/runtime/mathlib \
  --work-dir /workspace/scratch/2771a9ff6f38/verification/conformal-balance/development \
  --target InfoGeometry.OperatorAlgebra.PeirceSpine.WilsonPlaquetteCriteria \
  --target InfoGeometry.OperatorAlgebra.SquareZeroUnitary
```

It exited zero. Every project module in this selected closure was compiled
from its recorded source snapshot; no borrowed project artifacts were used
in this run. The unchanged Mathlib cache was used at the exact pin. The
development `result.json` receipt has SHA-256
`cdf771fa48fcd02f9d295e10cff80499328e2e3dffe56ab8ed93d011fb7abbcf`.

The two reviewed and compiled source hashes are:

| Source | SHA-256 |
|---|---|
| `OperatorAlgebra/PeirceSpine/WilsonPlaquetteCriteria.lean` | `bb723ed4eeba4fced291d74a68203a5e87e60105fdce20cb48cfcbcb5f33061c` |
| `OperatorAlgebra/SquareZeroUnitary.lean` | `f272ec89b0acdb47343a2e450bb84fc973640486a4dcea8ff33bde855514e91d` |

The independent reviewer verified all 24 source snapshots against the
successful development run, checked the 22 unchanged dependencies against
their exact Git blobs at the base commit, and copied only those checked
dependency artifacts into an isolated artifact root. Both new owners were
compiled afresh. The native complete-declaration audit checked 12 declarations
in `WilsonPlaquetteCriteria` and eight in `SquareZeroUnitary`, including
generated helpers. The nine explicit theorem statements introduce no new
definitions.

The observed axioms were exactly `propext`, `Classical.choice`, and
`Quot.sound`. No proof hole, custom axiom, unsafe declaration, or partial
declaration was accepted. Both independent owner logs are empty and the
native audit completed without warnings. The four inherited dependency
warnings are recorded separately; no warning-suppression change was made.

The successful independent invocation, from the task workspace, was:

```bash
source /workspace/scratch/2e3cbf77ee2a/runtime/environment.sh
python3 /workspace/scratch/2771a9ff6f38/verification/conformal-balance/qa/run_qa.py \
  --repo /workspace/scratch/2771a9ff6f38/info-geometry-lean \
  --reference /workspace/scratch/2771a9ff6f38/verification/conformal-balance/development \
  --mathlib /workspace/scratch/2e3cbf77ee2a/runtime/mathlib \
  --lean /workspace/scratch/2e3cbf77ee2a/runtime/lean-4.34.1-linux/bin/lean \
  --development-log /workspace/scratch/2771a9ff6f38/verification/conformal-balance/development.log \
  --work /workspace/scratch/2771a9ff6f38/verification/conformal-balance/qa/final
```

It exited zero without a retry. The task-local runner used the repository's
unchanged `tools/quality/reviewed_audit_source.py` native audit implementation.
The existing runtime environment and executable-path compatibility shim
were used in both verification runs.

| Independent evidence | SHA-256 |
|---|---|
| `qa/final/qa-result.json` | `f0853b166ff8c48b721b1b28e81122c2434bbfd13d5707f12ef49b91c6345a93` |
| `qa/final/declaration-audit.log` | `3fd59a34ce36638559add920becd297854ce7ffcb43280d2866bea9f57d39ffc` |
| `qa/run_qa.py` | `a80b55d0047e81ec2ed25664d8c7a7d5c6f4c15d8de1be8a452eccbc0375553b` |

These task-workspace paths are relative to
`verification/conformal-balance/`.

This evidence is scoped to the stated source closure and theorem types.
It does not certify a whole-repository build or any of the open analytic
and categorical identifications in the ledger.

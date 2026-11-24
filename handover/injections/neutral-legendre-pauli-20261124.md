# Native neutral, Legendre, Pauli-incidence, and corner bridges

## Intake and revision

This follow-on task starts from published PR #435, commit
`bb62f7aa71c69eb04576b95c7d5333baf0054225`, tree
`594b53e172b3a63622ad4d3b9d3c5f6cd1675b45`. The new branch is
`codex/neutral-legendre-pauli-20261124`. The parent PR's uncompleted compiler
and axiom checks are not evidence of mathematical acceptance of this packet.

The two supplied texts are preserved as the original user attachments:

| Source | SHA-256 | Role |
| --- | --- | --- |
| `Pasted text(20261124-075635).txt` | `35f52a95103beeb243802d15678fe840bab0d62274bff6cfcdea50b784d18200` | Informal mathematical narrative |
| `Pasted text (2)(20261124-075642).txt` | `7d8119b046ddfedd874ad93dfc14d683de7e583cad679354f68de673079c3378` | Proposed repository inventory and monolithic Lean candidate |

Claims of verification in the attachments are intake claims. They are not
compiler receipts. The uploaded monolithic source is not copied into an owner.

## Intent envelope and claim ledger

The intended output is a small set of native algebraic bridges. The carriers
and their maps remain explicit; conceptual proximity does not supply a map.

| Intake atom | Existing owner and precise scope | Task disposition |
| --- | --- | --- |
| Primal/dual grading, neutral metric, skew pairing | `Clifford.NeutralPhaseSpaceCore`: `V × Module.Dual ℝ V`, native bilinear forms, para cut, nondegeneracy under stated module hypotheses | Reuse; do not define another finite para carrier |
| Symmetric Legendre graph is isotropic | `Geometry.DualFlatKreinLegendreGraph`: `IsSymmetricDuality L` and pairwise skew-pairing vanishing | Strengthen to equality of a native graph submodule and its skew orthogonal complement |
| Neutral graph complement | Same native primal/dual carrier and symmetric linear duality | Prove neutral orthogonal of `L.graph` equals `(-L).graph` |
| Coordinate maximality | Native products `⊤ × ⊥` and `⊥ × ⊤` | Prove equality to their orthogonal complements; expose dual-separation hypothesis |
| Quadratic conjugate | `OperatorAlgebra.OperatorDirichlet.MatrixLegendre`: symmetric invertible completion of square and positive-definite `legendre_conjugate_isGreatest` | Connect to the actual continuous-dual `Convex.fenchelConj`, with positive definiteness explicit |
| Fenchel/Bregman gap | `Convex.Bregman` and the same full symmetric matrix quadratic form | Identify the exact weighted square and equality condition; no diagonal reduction |
| Plücker polynomial and determinant | `Projective.ExteriorKleinCoordinateIncidence.det_rows_eq_incidence` and `kleinIncident_iff_coordinate_incidence`; the latter uses `NondegenerateExteriorFrame` | Reuse the full existing independent-frame intersection criterion; a polynomial identity alone does not prove the unrestricted geometric iff |
| Real Pauli null incidence | `Canonical.RealPauliPfaffianKernel` and `Twistor.RealTwistorIncidence` | Connect the existing real 4×4 Pauli matrices to native incidence submodules and the determinant/kernel iff |
| Graph dimension | `RealTwistorIncidence.spinorEquivIncidence` | Prove dimension four over ℝ; the ambient real space has dimension eight |
| Phase compatibility | Existing `realPhaseAxis` and `pauli_commutes_phase` | Prove the existing phase preserves each real incidence submodule; no new complex scalar carrier |
| Same-corner products vanish | `PeirceSpine.Basic.conePlus_mul_conePlus` and lower-corner counterpart | Reuse without another wrapper |
| Symmetric corner triple | `PeirceSpine.Bergman.jordanTriple = XYZ + ZYX`; `TripotentExtremalJordanPair.jordanTriple_mem_extreme_intersection` already owns real-algebra opposite-grade closure | Add direct heterogeneous Peirce support closure over arbitrary associative rings using that operator |
| Square-zero Jordan associator | `Core.JordanAssociatorRing` and normalized `Core.JordanAssociator` | Connect existing symmetrized product to the existing triple, with the normalization factor stated |
| Clifford/Lipschitz action | `Clifford.LipschitzVectorAction` already constructs the twisted action and isometry homomorphism under explicit hypotheses | Reuse; uploaded ordinary conjugation with an assumed map is not a new full Clifford-group construction |
| Trace infinitesimal identity | Declaration `InfoGeometry.Physics.matrix_trace_commutator_pairing` in module `Physics.MatrixTraceBimodulePairingNative` | Existing identity gives `trace([H,μ]K)=0` when `HK=KH`; no duplicate trace API |

## Exact theorem contracts

### Neutral graph submodules

Carrier: an arbitrary real module `V` and `V × Module.Dual ℝ V`.
Operations: existing `canonicalNeutralBilin` and `neutralOmega`; Mathlib's
right-orthogonal convention. Map: `L : V →ₗ[ℝ] Module.Dual ℝ V`, with the
existing symmetry predicate `(L u) v = (L v) u`.

Targets: `neutralOmega.orthogonal L.graph = L.graph` and
`canonicalNeutralBilin.orthogonal L.graph = (-L).graph`, plus the coordinate
product equalities. The dual coordinate result explicitly retains the
module-projectivity/separation hypothesis required by the native dual API.
These strengthen pairwise isotropy to actual submodule equalities. They do
not construct a smooth manifold, connection, or closed differential form.

### Matrix Fenchel and Bregman

Carrier: arbitrary finite real coordinate modules with their native continuous
dual. Matrix: an arbitrary positive-definite real matrix `A`; its symmetry and
invertibility are obtained from existing owner lemmas. The covector for `y`
is `(dotProductBilin ℝ ℝ y).toContinuousLinearMap`.

Targets: the actual conjugate of `x ↦ (1/2) * quadForm A x` equals
`(1/2) * quadForm A⁻¹ y`; the Fenchel gap equals
`(1/2) * quadForm A (x - A⁻¹ *ᵥ y)`; it vanishes exactly at `y = A *ᵥ x`.
The existing algebraic-covector Bregman divergence is identified with the
corresponding weighted square. The algebraic covector is specified explicitly;
no derivative theorem or global smooth Legendre-diffeomorphism claim is made.
This is a canonical reformulation: the candidate uses `A.PosDef` and `A⁻¹`.
It does not separately identify the supplied `GInv` with `A⁻¹` or derive
positive definiteness from the attachment's inverse/nonnegativity packet.

### Real Pauli incidence

Carrier: `S = Fin 4 → ℝ`, incidence vectors in `S × S` in the existing
`(ω,π)` convention. The operator is `Matrix.toLin' (pauli t x y z)`.
The incidence submodule is the existing `incidenceSpace`, not a new predicate.

Targets: dimension four, injective dependence on the four real coordinates,
equivalence between null displacement and a nonzero shared incidence vector,
and preservation by the pair of existing phase endomorphisms. Null separation
uses the exact mostly-minus `intervalSq` and the existing real determinant
identity. These are real four-dimensional submodules in a real
eight-dimensional ambient space. No real `Gr(2,4)` identification or complex
Grassmannian transport is inferred from a matrix name.

### Peirce corner triple

Carrier: a general associative ring, without commutativity assumptions.
Cut: `P * P = P`; existing `conePlus P A = P*A*(1-P)` and
`coneMinus P C = (1-P)*C*P`. Operator: existing
`jordanTriple X Y Z = X*Y*Z + Z*Y*X`.

Targets: heterogeneous outer corner inputs yield the same corner after the
triple, and for a square-zero input the unnormalized Jordan associator is
the diagonal triple. With the normalized real-algebra product
`x ∘ y = (1/2) • (xy+yx)`, the corresponding associator is
`(1/4) • jordanTriple x y x`. Retain arbitrary noncommuting operators.
The source's isolated equation `X + XYX = 2XYX` is not a general Jordan
identity and is not promoted.

## Established dependency order

1. Native primal/dual bilinear forms and a symmetric duality map imply the
   graph orthogonal-complement equalities.
2. Matrix positivity implies invertibility, the completed-square bound and
   attainment; `IsGreatest` identifies the genuine `fenchelConj` value.
3. The Pauli displacement determinant law and the native graph/kernel iff
   imply the null/shared-incidence iff. The existing linear equivalence
   fixes graph dimension independently of the null condition.
4. Idempotent corner support and the existing associative Jordan identities
   imply corner closure and the normalized/unnormalized associator formulas.

There is no asserted implication from one of these four chains to another.
The Clifford twisted action and cyclic-trace identities remain separate
existing algebraic chains.

## Adjacent open or conditional claims

- Smooth para-Kähler geometry, integrability, connections, and global Legendre
  maps need their own analytic/manifold constructions.
- A Plücker determinant criterion for nonzero plane intersection requires
  genuine rank-two frames or native dimension hypotheses. The unrestricted
  version is false: `u=v=e₀`, `s=e₁`, `t=e₂` gives determinant zero but disjoint
  spans. Existing `ExteriorKleinTwoPlaneIncidence` supplies
  `planesIncident_iff_exists_nonzero_mem` and
  `combinedFrame_wedge_eq_zero_iff_incident`; the generic
  `ExteriorBladeIncidence.ιMulti_mul_ιMulti_eq_zero_iff` explicitly requires
  independent frames. These established owners remain separate from the
  real four-plane Pauli graph construction.
- Ordinary conjugation, twisted Clifford action, a supplied vector map, and
  a constructed group homomorphism are different statements.
- The trace identity assumes a cyclic finite matrix trace. It does not supply
  an ODE, a differentiable momentum curve, a Souriau moment map, or a Type III
  trace.

## Validation plan and current disposition

The four new bridge modules add twenty theorem declarations and no new carrier
or operation definitions. Two prerequisite owners receive explicit-import
repairs: `OrientedPfaffianMatching` imports `Perm.Sign` rather than all of
Mathlib, and `MajoranaPfaffian4` explicitly imports the determinant owner it
uses. Existing statements and proof bodies are unchanged.

The strict model-construction gate also requires a local constructive matching
in the generic matching owner; its earlier concrete examples live only in the
downstream Pfaffian owner. `PerfectMatching.doubled` now constructs a genuine
matching on every doubled index type `α ⊕ α` using `Sum.swap`, with two simp
readouts. It assumes no pre-existing matching. This is one new generic
construction and two computation lemmas, rather than an empty or assumed
witness.

`verification/neutral-legendre-pauli/check.py` selects these six owners and
reuses the existing focused-package shared-lock runtime. The shared verifier
is parameterized without changing its original Dirac-packet defaults. The new
entrypoint inventories 44 explicit public heads, plus eleven separately named
reused declarations: **55 planned axiom records**, not yet observed records.

Source generation, independent semantic audit, and acceptance QA have separate
agents. Before promotion, run focused builds and fresh warning-as-error checks,
audit the actual axiom dependencies of every added declaration, and run the
repository's staged/source gates. Keep exact pins and serialize compiler work
under the shared lock. Record the exact checked source hashes and commands.

## Recorded validation outcome

**Disposition: source review and static gates passed; compiler acceptance is
blocked. These remain theorem candidates, not kernel-verified results.**

Independent source review approved all six changed Lean owners, the verifier
parameterization, the new entrypoint, and the stated interpretation boundaries.
The final six static commands all returned exit `0`:

| Check | Result |
| --- | --- |
| `proof_proxy_staged_gate.py --strict` on the six changed Lean files | Passed |
| `semantic_vacuity_gate.py --fail-on error` on those files | Passed; five nonblocking lexical warnings |
| `semantic_content_audit.py --file-prefix <each of the six files> --gate` | Passed; zero findings |
| `opengauss_screener.py <six files> --strict --json` | Passed; zero findings |
| `opengauss_cli.py refute <six files> --strict --json` | Passed; zero findings |
| `opengauss_cli.py review <six files> --gate GATE_4 --json` | Passed; static review only |

The five lexical warnings concern the existing `pfaffian4_matching_expansion`,
the `PerfectMatching.fixed_free` structure field, the existing
`permutation_apply`, and the two new `doubled_partner_*` computation lemmas.
The short computation lemmas expose actual definition behavior; the field is
a matching invariant discharged by the new construction. No mathematical
acceptance is inferred from this classification.

Earlier rejected snapshots are retained separately: the first rejected the
direct scalar `linarith` step in the matrix gap proof (T16); the second still
rejected the generic matching owner for lacking a local construction (T17).
The final source expresses the scalar rearrangement through additive
equalities and includes the genuine doubled-index construction. No gate was
weakened or disabled.

The focused invocation was:

```bash
python3 verification/neutral-legendre-pauli/check.py \
  --repo /tmp/info-geometry-pr-973799e9818b \
  --output /tmp/real-dirac-publication-recovery/new-intake/qa/focused-run-001
```

Its source/pin preflight produced the expected 44-head inventory and a fresh
55-name axiom probe. For this host, only the focused package's `packagesDir`
paths were temporarily redirected to an existing ordinary, clean cache whose
nine package revisions and origin URLs matched the manifest. Root pins,
toolchain, proof sources, and the maintained shared-lock wrapper were
unchanged. A host-local forwarding guard would recheck the packages under
the lock before launching the pinned Lake executable.

The first runtime/version command remained queued behind an external
`shared-formalism:2` build lock. There were **zero guard events, zero Lake
invocations, zero compiler checks, and zero observed axiom records**. The
queued session was cancelled with exit `130` before any Lake invocation.
Cancellation ended the execution namespace before its `finally` receipt was
written, so the two focused configuration files were restored manually from
their saved original bytes. Post-restoration inspection confirmed exact
original hashes and no unstaged differences. The external build was not
interrupted.

The authoritative host outcome is the cancellation/restoration receipt, not a
completed checker summary: the checker did not produce one. Root integration
and pre-push build gates have not passed. Draft publication is for review;
fresh compilation, the actual 55-record axiom audit, and root integration
remain acceptance debt. The source gate result is not a whole-repository
certificate.

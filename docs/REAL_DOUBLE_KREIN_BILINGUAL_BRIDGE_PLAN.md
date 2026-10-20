# Real Doubled-Krein Bilingual Bridge

## Purpose

This plan defines a real-linear bridge between the repository's doubled-Krein
spaces, real Clifford/matrix operators, and the Klein glide representation.
It deliberately avoids complexification.  The target is a collection of
kernel-checked morphisms and equivariance theorems, not a new replacement
carrier and not a physical interpretation layer.

## Scope and non-goals

### In scope

1. The real doubled carrier (V_+ \oplus V_-).
2. Its neutral off-diagonal Krein pairing.
3. The real grading and sheet-swap operators.
4. A real Clifford or matrix representation on that carrier.
5. The relation between Clifford generators and the grading/swap pair.
6. A real pullback representation of the Klein glide.
7. An explicit real-linear readout satisfying a proved equivariance square.
8. Transport of pairing, grading, projectors, and selected operator actions.

### Out of scope

- Complex scalar extension or (M_4(\mathbb C)).
- A claim that an affine glide is itself a linear Krein operator.
- A claim that every Möbius twist is involutive or invertible.
- A homeomorphism between a newly invented carrier and the Klein bottle.
- Infinite-dimensional completion, measure theory, or physical dynamics.
- Identification of (J^2=-1) with a sheet swap (C^2=1).

## Existing owners to inspect and reuse

The implementation must begin with repository-wide source inspection and
declaration tracing.  The principal owners identified so far are:

- `InfoGeometry.Synthesis.CategoricalInevitabilityPosetSynthesis`
  - `IsMobiusTwist`
  - `IsSheetSwapInvolution`
  - `paraProjectorPlus`, `paraProjectorMinus`
  - eigenspace and sheet-intertwining lemmas
- `InfoGeometry.Synthesis.AndreevKreinHestenesCuntzSynthesis`
  - real doubled-Krein carrier
  - neutral pairing and sheet swap
  - real matrix/Krein adjoint identities
- `InfoGeometry.Synthesis.RecoveredPhysicalInvariantsSynthesis`
  - double-real Krein pairing and block operators
  - isotropic sheet identities
- `InfoGeometry.Synthesis.Cl22RealDiracCarrier`
  - real (Cl(2,2)) matrix generators
  - (J_{geom}^2=-1), volume grading, projectors, and Andreev rotor
- `InfoGeometry.Topology.KleinBrillouinBase`
  - affine glide on the cover
  - torus involution after quotienting by periods
- `InfoGeometry.Topology.KleinBottleOrbitQuotient`
  - orbit setoid and quotient map
- `InfoGeometry.Synthesis.Cl22ModularWave18`
  - finite real-to-complex Gibbs bridge; use only as evidence for algebraic
    patterns, not as a dependency of this real-only plan

Before adding declarations, search all Lean files for existing definitions of
the doubled carrier, grading, swap, neutral pairing, Clifford action, and
glide pullback.  Reuse exact owners and do not create aliases with competing
namespaces.

## Proposed module layout

Create a focused module under `lean/InfoGeometry/Synthesis/` only after
confirming that no existing owner already provides the same theorem family.
The preferred name is:

```text
RealDoubleKreinBilingualBridge.lean
```

If the repository's owner graph identifies a more canonical namespace, place
the declarations there instead of introducing a forwarding module.

Keep the file small.  Split the work into helper owner files if the real
representation and the glide pullback require independent carriers.

## Mathematical contract

Let (V) be a real module and define the doubled carrier

\[
K(V) = V \times V.
\]

Write elements as ((u_+,u_-)).  The intended operators are:

\[
\Gamma(u_+,u_-)=(u_+,-u_-),
\qquad
C(u_+,u_-)=(u_-,u_+).
\]

For a chosen real bilinear pairing (b) on (V), define the neutral pairing

\[
g((u_+,u_-),(v_+,v_-))
 = b(u_+,v_-)+b(u_-,v_+).
\]

The first theorem layer should establish:

```lean
theorem grading_sq : Γ.comp Γ = LinearMap.id
theorem sheetSwap_sq : C.comp C = LinearMap.id
theorem sheetSwap_anticommutes_grading : C.comp Γ = -(Γ.comp C)
theorem neutralPairing_sheetSwap
theorem neutralPairing_grading
```

The exact theorem names and carrier types must follow the existing owners.
Do not introduce a wrapper structure merely to package these facts.

## Clifford/operator language

The real operator language must be an actual representation, not a formula
similarity claim.  Choose one of the existing real matrix or Clifford carriers
and prove a real algebra morphism

\[
\rho : A_{\mathbb R} \to \operatorname{End}_{\mathbb R}(K(V)).
\]

The minimum contract is:

```lean
theorem rho_add (a b : Aℝ) : ρ (a + b) = ρ a + ρ b
theorem rho_mul (a b : Aℝ) : ρ (a * b) = ρ a * ρ b
theorem rho_one : ρ 1 = 1
```

For the selected generators, prove the exact image identities.  The key
signature distinction is:

\[
J_{geom}^2=-1,
\qquad
\Gamma^2=C^2=1,
\qquad
(C\Gamma)^2=-1.
\]

Therefore the likely correct target is an identity of the form

\[
\rho(J_{geom}) = C\Gamma,
\]

or a proved variant determined by the existing matrix basis.  Never assert
\(\rho(J_{geom})=C\) without checking its square.

Required checks:

1. Generator squares and anticommutators.
2. Image of the real grading/volume element.
3. Image of the elliptic cross-sheet bivector.
4. Compatibility with the neutral pairing or Krein adjoint, where the owner
   provides the needed hypotheses.

## Bilingual equivariance layer

The two languages are:

1. **Sheet language:** (K(V)), (Gamma), (C), and (g).
2. **Operator language:** real Clifford/matrix multiplication and the map
   (ho).

The central comparison theorems are:

\[
\rho(a x)=\rho(a)\rho(x),
\qquad
\rho(\Gamma x)=\Gamma\rho(x),
\qquad
\rho(Cx)=C\rho(x),
\]

with the exact domains made explicit.  If ρ maps algebra elements to
operators, formulate these as commuting actions rather than ill-typed
equalities.

The implementation must state whether the representation is:

- faithful;
- merely an algebra homomorphism;
- pairing-preserving;
- grading-preserving;
- or only equivariant for a named subalgebra.

Do not infer faithfulness from a matrix realization unless injectivity is
proved.

## Klein glide representation

The owner `KleinBrillouinBase` defines the affine cover action

\[
G(x,y)=(x+\pi,-y),
\qquad G^2=T_x.
\]

The torus action is involutive only after the period quotient.  To obtain a
linear real representation, use pullback on a real function carrier, for
example

\[
(G^*f)(x)=f(Gx).
\]

The plan requires a precisely typed carrier for such functions and a proof of
linearity.  Then construct a real-linear readout

\[
\rho_K : F(X,\mathbb R) \to K(V)
\]

or a smaller owner-aligned coordinate carrier, and prove the equivariance
square

\[
\rho_K(G^*f)=C(\rho_K(f)).
\]

This is the theorem that connects the topological and Krein languages.  It
must be conditional on the explicit readout definitions and quotient
compatibility; the mere existence of a glide and a sheet swap is insufficient.

If a function-space construction is too large for the current owner graph,
first formalize the finite coordinate action and its real-linear readout.  Do
not promote that finite model to a topological equivalence.

## Projector and pairing transport

After the equivariance theorem, prove only the consequences that follow from
it:

1. (C) exchanges the Γ-positive and Γ-negative eigenspaces.
2. (C) exchanges the two grading projectors.
3. The neutral pairing is preserved under the sheet swap.
4. The operator-language image satisfies the corresponding transported
   identities.

Potential theorem contracts include:

```lean
theorem sheetSwap_maps_plus_to_minus
theorem sheetSwap_maps_minus_to_plus
theorem sheetSwap_intertwines_projectors
theorem glide_readout_equivariant
theorem glide_readout_pairing_compat
```

Use existing eigenspace and projector lemmas whenever possible.

## Causal dependency order

The proof DAG is:

1. Existing real module and pairing owners.
2. Doubled carrier operations.
3. Grading and sheet-swap algebra.
4. Projectors and eigenspace transport.
5. Real Clifford/matrix representation.
6. Generator image and square/sign checks.
7. Operator/pairing compatibility.
8. Real glide pullback action.
9. Readout construction.
10. Glide/Krein equivariance.
11. Transported pairing and projector consequences.

No later theorem may be used as an assumption for an earlier layer.

## OpenGauss execution protocol

For each theorem wave:

1. Search all relevant Lean folders and read owner files.
2. Write an exact theorem contract with carrier and hypotheses.
3. Have an audit agent review the candidate proposition for vacuity and
   category errors.
4. Have a proof agent write only a new candidate file under `/tmp`.
5. Run `lake env lean` on the candidate.
6. Run the OpenGauss strict screen.
7. Run semantic-vacuity and placeholder scans.
8. Probe theorem axioms.
9. Promote the candidate into the repository only after all checks pass.
10. Stage immediately with `git add -A`.
11. Run the locked target build through the shared build lock.
12. Commit and push through the configured SSH route.

Builds must be sequential.  Never run `lake clean`, delete `.lake`, use
`git restore`, or modify dependency pins.

## Audit questions for every candidate

- Is the theorem about the actual owner carrier?
- Is the map linear over ℝ, or is that merely inferred from notation?
- Are all domain and codomain types explicit?
- Does a claimed involution really have square equal to identity?
- Is a topological affine action being confused with a linear operator?
- Is a Clifford (J^2=-1) generator being confused with a grading (K^2=1)?
- Are pairing and adjoint claims backed by the correct hypotheses?
- Does a quotient statement use the actual quotient owner?
- Is the result an equivalence, an embedding, or only an intertwining relation?
- Are there hidden witnesses, wrappers, `True` goals, `sorry`, `admit`, or
  custom axioms?

## Acceptance criteria

The bridge is complete only when all of the following are kernel-checked:

1. Real doubled-Krein grading and swap laws.
2. Real Clifford/operator representation laws.
3. Correct identification of elliptic versus involutive generators.
4. Pairing and projector transport.
5. A typed real glide pullback action.
6. A typed real readout map.
7. The glide/Krein equivariance theorem.
8. No false homeomorphism or physical claims.
9. Zero `sorry`, `admit`, placeholder, vacuous theorem, or custom axiom in
   the new owner files.
10. Locked build, OpenGauss strict audit, semantic-vacuity audit, axiom probe,
    and pre-push quality gate all pass.

## Expected deliverables

- One small owner-aligned real bridge module, or several focused modules if
  the existing architecture requires separation.
- Exact theorem names and source locations recorded in the project ledger.
- A dependency note identifying which claims are equivalences and which are
  only one-way morphisms or equivariance results.
- Build and audit logs attached to the commit record.

## Repository-wide duplicate audit (2026-10-20)

The search was expanded beyond `InfoGeometry/Canonical`. It covered every
Lean source under `lean/`, including `Algebra`, `Algebraic`, `DAG`,
`Experimental`, `Epistemology`, `Krein`, `Optics`, `OperatorAlgebra`,
`Physics`, `Synthesis`, `Topology`, and `Twistor`, and it also covered the
repository-level `proofs/` tree. Hidden `.kilo/worktrees` and `external_refs`
were searched as historical or external evidence, not as active owners.

### Active owners found

* `InfoGeometry.Krein.DoubledSpace` is the native real carrier
  `WithLp (2 : ENNReal) (E × E)` and owns `modular_j` and
  `spectral_epsilon`.
* `InfoGeometry.Canonical.BilingualRealHestenesDictionary` is already the
  bilingual real dictionary. It proves the phase-axis/`complex_i` readback,
  real `Cl(1,1)` relations, complex-linear and complex-antilinear readbacks,
  Krein anti-isometry, inner-product identities, and the Hestenes pseudoscalar
  readback. A second bilingual carrier must not be introduced.
* `InfoGeometry.Canonical.RealDoubledCliffordFiniteSpine` is a projection layer
  over `DoubledSpace`; it owns the real finite `Cl(1,1)` relation aliases and
  the matrix comparison.
* `InfoGeometry.Canonical.RealDoubledKreinMirror` owns real-linear mirror
  conjugation, grade reversal, and involutivity.
* `InfoGeometry.Canonical.RealDoubledKreinMirrorTopological*` owns the
  continuous-operator extension, even/odd submodules, direct-sum reconstruction,
  and the diagonal action `(u,v) ↦ (u,-v)` with its equivariance theorem.
* `InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinNative` owns a distinct
  cross-sheet Krein polarization on the same real `DoubledSpace` carrier and
  proves native `KreinSpace` adjoint, self-adjointness, and unitary readbacks.
* `InfoGeometry.Krein.RealDoubledHilbertBridge` transports the real carrier to
  the Hilbert-doubled presentation and proves conjugation identities for the
  swap, grading, and complex-structure composites.
* `InfoGeometry.Topology.KleinBrillouinBase` and
  `InfoGeometry.Topology.KleinBottleOrbitQuotient` own the affine glide,
  torus involution, orbit setoid, and quotient map. Their carrier is a torus
  quotient, not `DoubledSpace`.

### Non-Canonical and proof-tree evidence

The `lean/Experimental` and `lean/DAG` trees contain finite or abstract
variants, but no replacement for the native real `DoubledSpace` owner. The
repository `proofs/` tree contains useful already-proved algebraic patterns:

* `proofs/KreinDoubling.lean`: real block-matrix Cartan doubling and transpose
  sign transport;
* `proofs/TwoSheetKreinAdjoint.lean`: finite sheet-flip Krein adjoint on a
  complex six-state matrix carrier;
* `proofs/KleinGlideCovering.lean`: the torus glide quotient as a genuine
  `ZMod 2` covering;
* `proofs/KleinSixStateBundle.lean`: an abstract matrix-family glide
  equivariance law and its involutive consequence;
* `proofs/ModularKreinReflectionColimit.lean`: a stagewise real linear
  reflection commuting with every iterated bonding map;
* `proofs/ZornKleinGlideBridge.lean`: a paired Zorn/affine glide, with square
  and transverse-conjugation relations;
* related `proofs/KleinSixStateBundleOrbitEquiv.lean` and Klein quotient files:
  finite quotient/bundle constructions.

These proof files are not interchangeable owners: several use complex matrix
fibres, abstract function carriers, or supplied equivariance data. They are
precedent for theorem shapes only. The proof-tree search did not find a
theorem whose type is a real-linear equivariance square from the affine
`KleinBrillouinBase.torusGlide` action directly to the native
`InfoGeometry.Krein.DoubledSpace` sheet swap.

### Duplicate classification

The exhaustive lexical scan reports many occurrences because the same words
appear in active owners, applications, audits, generated snapshots, and
historical worktrees. The carrier-level duplicates are:

1. `DoubledSpace E` references: many consumers, one owner in
   `Krein/DoubledSpace.lean`;
2. pair carriers (`E × E`, `ProofSpace`, `CarrierDoubled`): independent
   simplified models in epistemology, synthesis, and proofs;
3. finite matrix sheet flips: separate `M₂`, `M₆`, and block-matrix models,
   not definitional duplicates of `DoubledSpace`;
4. complex two-sheet carriers: `BipolarTwoSheetCore` and related modules,
   explicitly outside this real-only plan;
5. archive/recovery and `.kilo/worktree` copies: provenance or stale mirrors,
   not active theorem owners.

No direct declaration matching `torusGlide`/`glide` equivariant with
`DoubledSpace`, `modular_j`, or the real bilingual dictionary was found in the
active non-Canonical trees or in `proofs/`. This is a bounded lexical and
declaration search result, not a claim that no semantically equivalent theorem
could exist under an unrelated name; the owner/import scan is the basis for the
remaining gap.

## Revised implementation order after the duplicate audit

1. Reuse `DoubledSpace`, `modular_j`, `spectral_epsilon`, and the existing
   bilingual dictionary; do not add a carrier or a complexification.
2. Reuse the real mirror/topological direct-sum owners for sheet and
   operator-sector identities.
3. Reuse `KleinBrillouinBase`/`KleinBottleOrbitQuotient` only for the base
   affine/quotient action; do not identify the quotient with the Krein carrier.
4. First prove the smallest finite coordinate readout theorem: a chosen
   real-linear map from a finite glide-coordinate carrier into `DoubledSpace`
   intertwines the explicitly defined involution with `modular_j` (or the
   exact sheet-swap owner selected by the map).
5. Only then extend the readout to a function-space pullback or quotient
   descent, if the required topology and continuity data are available.
6. Use proof-tree covering and equivariance theorems as subordinate lemmas
   only after their carriers are explicitly related by a proved map.
7. Compile the smallest owner-aligned file, then run the locked target build,
   placeholder/vacuity checks, and axiom inspection. Unproved topological
   classification or physical interpretation remains outside the theorem
   surface.

### Additional non-Canonical duplicate findings

The all-folder definition scan found two further real implementations that
must be distinguished explicitly:

* `lean/SelfReference/Krein.lean` defines the lightweight algebraic carrier
  `SelfReference.DoubledSpace E := E × E`, with `modularJ`,
  `spectralEpsilon`, and `complexI` as ordinary `LinearMap`s.  This is a
  separate, topology-free pair carrier; it is not definitionally equal to
  `InfoGeometry.Krein.DoubledSpace E`, which is a `WithLp` carrier with
  continuous operators.
* `lean/InfoGeometry/Clifford/Cl11.lean` only re-exports the canonical
  `InfoGeometry.Krein.DoubledSpace` as an `abbrev` and forwards its continuous
  operators.  It is a compatibility surface, not a second owner.

The exact operator mismatch across the duplicate pair models is now recorded:

* native `modular_j`/`modularJ` is the sheet swap `(u,v) ↦ (v,u)` and squares
  to `+id`;
* `WheelerDelayedChoiceModularLaw.mobiusTwist` is the signed swap
  `(u,v) ↦ (-v,-u)` and also squares to `+id`;
* `WheelersOuroborosSynthesis.opJ` is the quarter-turn `(u,v) ↦ (-v,u)` and
  squares to `-id`;
* `SelfReference.complexI` is the corresponding quarter-turn
  `(u,v) ↦ (-v,u)` on the lightweight pair carrier;
* matrix proof files use yet other finite carriers (`M₂`, `M₆`, or block
  matrices), sometimes over `ℂ` rather than `ℝ`.

Thus the apparent Möbius/Krein disagreement is not a single theorem with a
wrong sign. It is an operator and carrier mismatch: an involutive sheet swap,
an involutive signed swap, and a complex-structure quarter-turn are being
given the same informal name. Any future bridge must state the selected map's
square and scalar base ring in its type.

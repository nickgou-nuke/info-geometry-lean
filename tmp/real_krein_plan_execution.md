# Execution plan: real Hilbert spaces and double real Krein spaces

## Scope and source of truth

This plan is for extending the real Hilbert/Krein lane while reusing the
existing owners. The kernel checked Lean declarations are authoritative. The
current worktree already contains an unrelated staged modification to
`docs/KASPAROV_KREIN_RECONCILIATION_PLAN.md`; preserve it and do not fold it
into this work.

The intended carrier conventions are:

- A real Hilbert space is a type `E` with
  `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]`.
- The canonical doubled carrier is
  `InfoGeometry.Krein.DoubledSpace E := WithLp (2 : ENNReal) (E × E)`.
- Its coordinate maps are `WithLp.fst` and `WithLp.snd`, with constructors
  `to_doubled`, `plusPoint`, and `minusPoint`.
- The doubled real symmetries are `modular_j` (sheet swap),
  `spectral_epsilon` (fundamental sign), and
  `complex_i = modular_j.comp spectral_epsilon`; the last one squares to
  `-id` and is a real-linear complex-like axis, not a change of scalar field.
- The canonical indefinite form is
  `KreinSpace.kreinInner`, backed by the repository's existing `KreinSpace`
  instance on `DoubledSpace E`.

Existing owners and bridges to reuse:

- `lean/InfoGeometry/Krein/KreinSpace.lean`: real `KreinSpace`, `jCLM`,
  `kreinInner`, `kreinAdjoint`, projector operators, and adjoint laws.
- `lean/InfoGeometry/Krein/DoubledSpace.lean`: doubled `WithLp` carrier,
  `modular_j`, `spectral_epsilon`, `complex_i`, the canonical Krein instance,
  `doubledHilbertBilin`, and the `Cl(1,1)` identities.
- `lean/InfoGeometry/Krein/SplitQuadratic.lean` and
  `lean/InfoGeometry/Krein/SplitQuadraticSheets.lean`: quadratic form,
  positive/negative sheets, and signed divergence interfaces.
- `lean/InfoGeometry/Krein/PolarizedSector.lean` and
  `lean/InfoGeometry/Krein/DoubleRealKreinProjectorPairing.lean`: spectral
  projectors and the projector-difference formula for the Krein pairing.
- `lean/InfoGeometry/Canonical/RealDoubledCliffordFiniteSpine.lean`: the
  projection surface for the finite real doubled Clifford spine (`J`, `ε`,
  `K`, `J_sq`, `epsilon_sq`, `K_sq`, and `doubled_cl11_relations`).
- `lean/InfoGeometry/Canonical/RealDoubledKreinMirror.lean` and
  `lean/InfoGeometry/Algebra/ChiralDoubledRealBlock.lean`: real-linear mirror,
  clock, grading, raising/lowering blocks, and mirror conjugation.
- `lean/InfoGeometry/Canonical/BipolarRealDoubledKreinBridge.lean`:
  complex phase readout through existing real operators; this is an adapter,
  not a complexification of the carrier.
- `lean/InfoGeometry/Categorical/TwoSheetKreinFilteredColimit.lean`: the
  filtered-colimit transport interface for stagewise real two-sheet laws.
- `lean/InfoGeometry/Krein/HilbertBridge.lean`: type-distinct `ULift` wrappers
  and real Hilbert/Krein transport when a consumer needs a distinct carrier.

## Phase 0 — baseline and theorem contract

1. Read `AGENTS.md`, `docs/CANONICAL_AGENT_PIPELINE.md`,
   `docs/HIVE_AGENT_COMMANDMENTS.md`, `docs/REPO_DEEP_SEARCH_PROTOCOL.md`,
   and `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md`.
2. Record `git status --short`, `git log -1 --oneline`, active compiler
   processes, and the exact current owner-file hashes. Do not revert or edit
   the unrelated staged reconciliation document.
3. Search all repo-owned Lean code for `KreinSpace`, `DoubledSpace`,
   `modular_j`, `spectral_epsilon`, `complex_i`, `kreinInner`, `KreinHom`,
   `RealKreinSpace`, `HilbertDoubled`, `plusSheet`, `minusSheet`, and all
   bridge imports. Trace declarations, instances, theorem statements, and
   consumers before selecting an edit point.
4. Write a ground-truth contract before any Lean source change:
   - carrier and scalar field (`ℝ` throughout the base lane);
   - whether the desired result is a theorem, a reusable structure, or a
     bridge adapter;
   - exact existing declarations being reused;
   - the smallest source-confirmed gap;
   - adjacent claims that are explicitly out of scope.

**Gate 0:** no new abstraction is proposed until the search confirms that the
needed declaration is absent from the relevant owner surface. A bridge may
only transport a proved owner theorem; it must not introduce a duplicate
Krein or colimit implementation.

## Phase 1 — establish the real Hilbert substrate

Use the typeclass assumptions already used by `DoubledSpace` and
`KreinSpace`; do not invent a parallel `RealHilbertSpace` structure unless a
consumer truly needs a bundled object and the contract proves that no existing
Mathlib typeclass interface suffices.

Proof obligations:

- all real scalar actions and inner-product identities elaborate under
  `InnerProductSpace ℝ E`;
- completeness is available where continuous adjoints, `WithLp`, or bounded
  operator statements require it;
- any finite-dimensional statement adds an explicit
  `[FiniteDimensional ℝ E]` assumption rather than smuggling finite rank into
  a general Hilbert theorem;
- real symmetry is handled by `real_inner_comm` and real scalar identities,
  with no conjugation theorem imported merely to imitate the complex case;
- if a new projection is required, prove linearity/continuity and its
  idempotence on the actual carrier before deriving sheet membership.

Preferred validation artifact: a small owner-local theorem packet importing
only the existing owner. Keep it modular and reusable; do not put a large
capstone theorem in a bridge file.

**Gate 1:** `lake env lean <new-or-owner-file>` succeeds with no `sorry`,
`admit`, custom axiom, unsafe proof, or vacuous `True` wrapper. Check
`#print axioms` for the new declarations and accept only standard foundational
axioms.

## Phase 2 — canonical double real Krein construction

Build on `DoubledSpace E` and its existing instance rather than defining a
second product carrier. The implementation sequence is:

1. Reuse `DoubledSpace.ext`, `to_doubled`, `fst_to_doubled`, and
   `snd_to_doubled` for extensional proofs.
2. Reuse `modular_j_involution`, `spectral_epsilon_involution`, and
   `modular_j_spectral_epsilon_anticommute` for the `Cl(1,1)` relations.
3. Reuse `complex_i_sq` / `clockAxis_sq` for the real complex-like axis.
4. Reuse the canonical `KreinSpace` instance and `KreinSpace.kreinInner` for
   the indefinite form. The signed form must remain visibly
   `⟪J u, v⟫_ℝ` through the owner API.
5. For sheet statements, use `spectralPlusProj` and `spectralMinusProj` plus
   `PolarizedSector` theorems, not ad hoc coordinate predicates.
6. For operator symmetry, use `KreinSpace.kreinAdjoint` and existing
   `isKreinSelfAdjoint`/`isKreinSkewAdjoint` characterizations.

Minimum theorem packet for a new double-real owner or bridge:

- carrier/instance compatibility;
- `J² = id`, `ε² = id`, and `J ε = - ε J`;
- `K = J ε` and `K² = -id`;
- `P₊ + P₋ = id`, idempotence, and coordinate readback;
- `KreinSpace.kreinInner` equals the positive-minus-negative projector
  pairing, via `DoubleRealKreinProjectorPairing`;
- mirror conjugation preserves multiplication and reverses the declared
  operator grade, via `DoubledHestenesKreinData`;
- if an operator is introduced, prove its exact Krein adjoint law and state
  the direction of composition explicitly.

**Gate 2:** compile the owner module and its direct audit module. The audit
must inspect theorem statements and axioms, not just imports. A narrow green
check does not establish compatibility with all consumers; run a repository
search for each changed declaration and inspect every dependent owner.

## Phase 3 — bridge existing finite and two-sheet structures

Only after the finite carrier packet is closed, add the smallest bridge needed
by the target consumer.

### Finite Clifford and block lane

Use `RealDoubledCliffordFiniteSpine` for the finite projection and
`ChiralDoubledRealBlock` for block operators. Required checks include:

- `doubledKreinEta_sq` and `doubledSwap_sq` remain the exact real-linear
  identities;
- `doubledSwap_conjugates_eta` and `doubledSwap_conjugates_clock` preserve
  the sign convention;
- raising/lowering blocks are transported through
  `DoubledHestenesKreinData.mirrorConjugate` and their grades are proven with
  the existing commutator definition;
- no matrix-level replacement is introduced for the categorical or owner
  declarations.

### Bipolar and phase readout lane

Use `BipolarRealDoubledKreinBridge` only to read complex phase data through
`doubledRealComplexScalar`, `clockAxis`, and the existing real doubled
Clifford spine. Keep the carrier, operators, and proofs real-linear. Prove
the round trip from the bridge to the owner operator (`zero_one` axis and
phase addition) before adding downstream phase theorems.

### Two-sheet filtered-colimit lane

Instantiate `Categorical.TwoSheetKreinFilteredColimit` only from a real stage
diagram and a stage natural transformation. Prove stagewise involutivity and
the commuting exchange equation first, then use
`colimitEnd_involutive`, `colimitEnd_exchange`, and
`colimitEnd_exchange_on_stage`. Do not assert a topological or analytic
continuum theorem from this interface alone.

**Gate 3:** direct owner and bridge checks pass independently. Every new
carrier map has an explicit source and target, every symmetry has a proved
compatibility equation, and every colimit law is inherited from the stage
diagram rather than reconstructed by analysis.

## Phase 4 — consumer closure and verification

For each consumer importing the changed owner:

1. Run `lake env lean` on the owner and direct bridge files.
2. Inspect compiler processes before any build; concurrent compiler/build/test
   jobs are forbidden.
3. Run the repository lock wrapper for the affected module target:

   ```bash
   python3 tools/infra/run_locked_lake_build.py \
     --wait-for-build-lock InfoGeometry.Krein.<Target>
   ```

   Substitute the actual target identified from `lakefile.lean`; do not guess
   a target name.
4. Run `git diff --check` and the applicable proof-proxy, axiom, vacuity,
   frontier, and semantic gates. Use the repository's maintained gate scripts
   and report exact commands and outputs.
5. If a source file was changed, stage it immediately with `git add -A` and
   record the staged path. Do not stage generated `artifacts/`, runtime, or
   cache debris unless explicitly requested.

The final report must name the exact declarations proved, owner files checked,
consumer modules checked, remaining closure debt, and any theorem whose
semantic interpretation is intentionally left unclaimed.

## Forbidden shortcuts and failure modes

- Do not replace a real Hilbert carrier by `ℂ`, a complex inner product, or a
  scalar toy model. Complex values may appear only as an explicit readout
  through an existing bridge with a proved map.
- Do not define a second `DoubledSpace`, `KreinSpace`, fundamental symmetry,
  projector pair, or colimit abstraction under a new name.
- Do not use `Complex.conj`, complex sesquilinearity, or a complex adjoint as a
  substitute for the real bilinear `KreinSpace.kreinInner` and real adjoint
  laws.
- Do not infer `K² = -id` from prose: prove it from the existing
  `modular_j`/`spectral_epsilon` anti-commutation and owner theorem.
- Do not identify the sheet swap `modular_j` with the sign symmetry
  `spectral_epsilon`; they have different carrier actions and different
  geometric roles.
- Do not transport a finite matrix identity to a continuum or filtered
  colimit using measure theory, analytic continuation, or an unproved density
  assertion. Use the categorical colimit owners and stage compatibility.
- Do not use docs, graph hits, generated transcripts, CAS output, or an oracle
  answer as proof authority. They are navigation or statement-shaping input;
  Lean owner declarations and kernel checks decide truth.
- Do not use `sorry`, `admit`, `axiom`, `unsafe`, opaque witness fields,
  assumptions that restate the conclusion, theorem aliases that hide an
  unproved claim, or a `: True` wrapper.
- Never run `lake clean`, delete `.lake/build`, delete `.lake/packages`, or
  run concurrent Lake/Lean/test commands. Never kill an active compiler task
  without explicit authorization.

## Completion criteria

The execution is complete only when the real Hilbert substrate, doubled real
Krein identities, requested bridge theorem(s), and all affected consumers have
kernel-checked proofs; the relevant audit and quality gates are green; no
forbidden complex shortcut or duplicate owner was introduced; and the staged
diff contains only the intentionally changed source plus this plan artifact.

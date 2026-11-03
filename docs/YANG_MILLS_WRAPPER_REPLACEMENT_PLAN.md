# Yang–Mills Archetype Poset and Theorem-Proof Plan

## Purpose

Organize the Yang–Mills work as a causal poset of mathematical archetypes.
Each archetype is to be established by genuine, reusable lemmas and theorems
on its actual carrier. The existing Peirce, matrix-valued differential-form,
topological, lattice, finite QFT, and colimit work is connected only where a
proved map justifies the edge.

The construction follows the repository's finite-stage architecture and then
the existing inductive-colimit carriers. The target is a truthful, composable
Lean API whose finite archetypes and colimit transport edges are proved in
their actual carriers.

## Grounded starting point

The relevant source owners currently separate into these lanes:

1. `lean/InfoGeometry/OperatorAlgebra/PeirceDefectBridge.lean` defines the
   inner grading derivation `[P, ·]`, Peirce covariant derivative, and
   Maurer–Cartan curvature. It proves the curvature decomposition and
   covariant constancy of `genV` from an idempotent cut.
2. `lean/InfoGeometry/Canonical/SelfDualConnectionCurvatureYangMillsBridge.lean`
   specializes the Peirce data to matrices over an exterior algebra. Its
   connection-curvature identification requires an explicit derivative
   compatibility premise. The zero-derivative specialization is algebraic.
3. `lean/InfoGeometry/Canonical/CurvatureFromConnectionBianchiBridge.lean`
   derives Bianchi from hypotheses `d² A = 0` and a product-rule equation for
   `d (A * A)`, then obtains the self-dual and anti-self-dual equations.
4. `lean/InfoGeometry/Canonical/NonAbelianCovariantBianchiChernWeilBridge.lean`
   derives trace reduction from a cyclicity premise. The Chern-class,
   Chern–Simons, de Rham, and BRST modules are adjacent imported lanes; each
   claimed connection must be traced to an actual theorem, not inferred from
   imports alone.
5. `lean/InfoGeometry/Canonical/TwoSheetedYangMillsInductiveColimit.lean`
   transports Peirce identities through star-preserving ring maps and a
   separately defined inductive-cone interface. Its audit explicitly
   distinguishes those algebraic transport results from mass-gap and
   reflection-positivity claims.
6. `lean/InfoGeometry/Canonical/PeirceTetraktysColimitCoercivity.lean` builds
   on the nontrivial finite tensor stages and their owner-level inductive
   `Stage n` / `bondMap` / `ofStage` inductive colimit `Limit`, proving trace
   polarization and transported Peirce
   covariant constancy. Its current Yang–Mills theorem is a Peirce-derivation
   result; it is not yet the transport of the matrix exterior-form connection
   curvature theorem.
7. `lean/InfoGeometry/LatticeGauge/FinitePlaquette.lean` and
   `FiniteGibbsModel.lean` formalize finite link configurations, plaquette
   holonomy, gauge covariance, a finite action, and its Gibbs distribution.
   No colimit edge from this lattice carrier is presumed.
8. `lean/InfoGeometry/Canonical/YangMillsFiniteQFT.lean` and
   `YangMillsFiniteBridge.lean` package KMS/OS/Wightman-like predicates and
   finite gap data. The positive gap is part of the bridge data or is derived
   from the finite-dimensional Jacobian-coercivity hypothesis; it is not yet a
   spectral lower bound for a Yang–Mills Hamiltonian.
9. `lean/InfoGeometry/Canonical/YangMillsContinuum.lean` is a modular/KMS
   scaffold based on scalar Radon–Nikodym data and endomorphisms of a doubled
   Hilbert space. It is not presently connected by a proved map to the finite
   gauge-connection or inductive-colimit owners, so it is not part of the
   finite-to-colimit Yang–Mills poset until such a map is proved.
10. `lean/InfoGeometry/Canonical/YangMillsBridge.lean` is an empty namespace
    facade over the finite umbrella; `YangMillsFinite.lean` is also an import
    umbrella. These are module-level compatibility surfaces, not mathematical
    theorem owners. `lean/InfoGeometry/Unstable/YangMillsBridge.lean` contains
    compatibility aliases and delegated KMS results.

## Poset law

The primary artifact is the **archetype poset**, not a collection of
assumption-bundling wrappers. Do not introduce declarations named or shaped as
`Hypotheses`, `Contract`, `BridgeData`, or similar structures merely to store
the premises of a later theorem. State mathematically necessary premises
directly in the relevant theorem, and prove each archetype with component
lemmas on its real carrier.

Import facades may remain for module organization, but they are not poset nodes
and do not count as mathematical results. Theorems that merely repackage other
theorems may serve as a final synthesis endpoint only after the poset's
archetype nodes and edges have their own substantive proofs. Avoid parallel
aliases, empty namespace surfaces, duplicate archetypes, and vacuous nodes.

Every poset edge must be justified by a named theorem that transports the
source conclusion to the target archetype. Shared imports, similar names, or
parallel carriers do not create an edge. If the edge needs an additional
mathematical condition, expose that condition in the edge theorem and prove it
from a structure already present in the source carrier when possible. Never
rename an assumed premise as a proved result.

## Work sequence

### Phase 0 — Source inventory and archetype extraction

1. Search all repo-owned Lean files for Yang–Mills, connection, curvature,
   Bianchi, instanton, BRST, lattice, KMS, gap, and colimit declarations.
2. Trace each candidate's imports, exact type, proof body, and consumers. Label
   source edges as **direct theorem dependency**, **carrier transport**,
   **import-only adjacency**, or **name-only resemblance**.
3. Extract atomic archetypes and define each precisely by carrier,
   operations, theorem statement, and proven dependencies. Record necessary
   premises in the theorem contract, not in wrapper structures.
4. Draw candidate causal edges, then retain an edge only when a source theorem
   proves the required transport. Keep module facades out of the mathematical
   graph. Do not edit broad umbrella modules merely to reduce file count.

**Exit condition:** every poset node is a precise mathematical proposition
with a known owner; every edge has a stated proof obligation; no graph,
docstring, or benchmark label is treated as proof evidence.

### Phase 1 — Prove the differential-form archetypes

1. Inspect existing differential-form and exterior-derivative owners before
   defining another derivative API. Add only archetypes that fill an identified
   proof gap. Prefer the existing `FrechetOperatorDerivation` carrier
   (`Optics/OperatorDerivationForms.lean:107`) over generic `Module.End`
   derivatives: its `leibniz` field is part of the structure, not a separate
   hypothesis, so no Leibniz premise is ever bundled into a theorem statement.
2. Give the connection carrier its actual grading and state the differential
   as a degree-one Fréchet Leibniz derivation `d : FrechetOperatorDerivation ℝ
   (ExteriorAlgebra R V)` with `d.comp d = 0` on the relevant forms. The
   Leibniz rule `d (x * y) = d x * y + x * d y` is a field of the structure,
   visible in every theorem statement that uses `d`.
3. Prove reusable lemmas for matrix extension of `d`, the signed Leibniz rule
   (`d(A·y) = dA·y - A·d y` for homogeneous degree 1; `d(F·y) = dF·y + F·d y`
   for homogeneous degree 2), connection curvature `F_A = dA + A²`, and
   covariance under a proved gauge transformation.
4. Prove `d² A = 0` and the graded product rule from the Fréchet Leibniz
   structure, with degree/sign conditions visible in theorem statements. Use
   them as lemmas in the Bianchi proof rather than bundling them in a named
   hypothesis object.

**Exit condition:** the Bianchi archetype is proved for the defined connection
and curvature from the Fréchet Leibniz differential lemmas, rather than from a
bespoke unproved product-rule premise.

### Phase 2 — Prove and order the two duality archetypes

1. Keep `parityConj P` and the Peirce even/odd grading in the algebraic owner.
2. In the differential-form owner, construct the Hodge operator from an
   explicit finite-dimensional metric and orientation, or state exactly which
   Hodge axioms are assumed.
3. Prove its degree action, square/sign law, and compatibility with the
   curvature carrier before defining the Hodge-self-duality archetype.
4. Establish the instanton implication through component lemmas:
   Bianchi + self-duality implies `D_A (★F_A)=0`; Bianchi + anti-self-duality
   implies the same equation, with the signed linearity premise proved from the
   covariant derivative definition.

**Exit condition:** the poset distinguishes Peirce parity duality from
spacetime Hodge duality; no edge between them exists without a proved map.

### Phase 3 — Prove the trace and topological archetypes

1. Replace blanket matrix cyclicity assumptions with a proved ordinary or
   graded-cyclicity theorem at the actual form degrees in use.
2. Prove `Tr(D_A X) = d Tr(X)` from that trace law and the differential
   definition.
3. Derive closedness of the relevant invariant polynomial from Bianchi,
   making the input curvature form and wedge/product degree explicit.
4. Connect closed forms to de Rham classes using the existing quotient owner;
   connect Chern–Simons transgression only after the exact differential is
   proved.
5. Keep BRST cohomology as its own complex until an explicit chain map or
   cohomology comparison with the gauge-curvature complex is established.

**Exit condition:** Chern–Weil and instanton-charge statements have explicit
graded trace, differential, and quotient premises, with no conclusion inferred
from imports alone.

### Phase 4 — Prove the Peirce-to-connection poset edge

1. Define a carrier map from the Peirce operator data to the chosen
   matrix-valued connection data.
2. Prove preservation of multiplication, grading, star, and the differential
   (or state the exact compatibility hypothesis if the map cannot preserve it).
3. Derive curvature and covariant-derivative compatibility as separate named
   lemmas; then shorten the current bridge theorem to their composition.
4. Keep the zero-derivative identity as a clearly labeled algebraic
   archetype, not as a model of the full geometric field equation.

**Exit condition:** the bridge maps both the connection and its curvature and
commutes with the relevant differential/covariant derivative; no prose
identification substitutes for those equations.

### Phase 5 — Prove finite-lattice archetypes and finite-stage transport edges

1. Keep the finite group-valued link and plaquette carrier as the lattice
   owner.
2. Prove gauge covariance of plaquette holonomy, gauge invariance of the
   chosen action, and compatibility of the finite Gibbs readout at the
   existing owners.
3. If connecting lattice data to matrix connections or the tensor stages,
   define the finite-stage representation and prove how links, plaquettes, and
   curvature transport at each stage.
4. Connect this lane to the inductive colimit only through the repository's
   actual compatible finite-stage maps and a proved colimit descent theorem.
   Do not infer that edge from a shared Yang–Mills label.

**Exit condition:** either a concrete representation/transport theorem exists,
or the lattice lane is explicitly reported as parallel and finite.

### Phase 6 — Prove finite QFT and spectral-gap archetypes on finite operators

1. Separate finite model inputs from derived results. In particular, do not
   put `spectral_gap_pos` in a data structure and then present its projection
   as a theorem proving the gap.
2. Define the finite Hamiltonian/operator, vacuum sector, and spectral notion
   of gap in the intended carrier.
3. Prove a coercive lower bound on the orthogonal complement of the vacuum
   from operator estimates; connect the bound to the Yang–Mills action only
   through a proved representation.
4. Keep KMS, reflection positivity, and reconstruction as separate
   propositions with their structural hypotheses; prove their compatibility
   with the same finite gauge model.
5. Retain `YangMillsMassGapAudit` as a warning that unconstrained scalar
   positivity does not imply a uniform gap. Do not use it as a Yang–Mills
   model or replace the operator problem with scalar energy variables.

**Exit condition:** a finite gap theorem refers to the spectrum of a defined
operator and is derived from nontrivial operator estimates, not from a gap
field in a structure.

### Phase 7 — Prove the finite-stage-to-inductive-colimit poset edges

1. Use the checked-in finite stage systems and owner-level inductive colimit
   `Limit` with their bonding maps. Do not substitute another carrier for this
   finite-stage-to-colimit construction.
2. Prove at finite stages that the bonding maps preserve the actual
   connection, curvature, trace, star, and covariant derivative used by each
   archetype.
3. Prove the corresponding compatibility and descent results into `Limit`;
   only then transport finite-stage Bianchi, gauge covariance, and curvature
   theorems.
4. Keep the modular/KMS lane separate unless a noncommutative finite-stage
   carrier map into the Yang–Mills stage system is defined and proved. Scalar
   Radon–Nikodym data times the identity alone does not supply that edge.

**Exit condition:** every target theorem is stated on a concrete finite-stage
carrier or the existing inductive-colimit carrier, with its compatibility
theorem proved from the finite stages.

## Progress record

Phase 0 (source inventory) — complete. Every Yang–Mills/connection/curvature/Bianchi
declaration was traced to its owner, carrier, and consumers (see inventory below).
Phase 1 (differential-form archetypes) — complete. `ExteriorDifferentialData`
(`Canonical/ExteriorGradedDerivationBridge.lean:23`) bundles `d`, `gradedLeibniz`,
`sq_zero` as structure fields; `GradedConnectionBianchiBridge` proves
`d²A = 0`, the signed 1-form Leibniz rule, and `D_A F_A = 0` from them
(`Canonical/GradedConnectionBianchiBridge.lean:30-79`), no bundled premise.
`FrechetOperatorDerivation` (`Optics/OperatorDerivationForms.lean:107`) has `leibniz`
as a structure field but requires `[NormedRing]`, so it cannot be instantiated on
`ExteriorAlgebra R V` here; `ExteriorDifferentialData` is the usable carrier.

Phase 2 (duality archetypes) — complete. `HodgeStarYangMillsSelfDuality`
states the Hodge square/sign law (`star² = s • id`, `s*s=1`) and degree-reversal
as explicit premises, and composes the existing instanton theorems
(`self_dual_solves_yang_mills`, `anti_self_dual_solves_yang_mills`).
Furthermore, `self_dual_connection_curvature_solves_graded_yang_mills`,
`anti_self_dual_connection_curvature_solves_graded_yang_mills`, and
`master_graded_connection_hodge_duality_synthesis` structurally compose the
graded Bianchi theorem (`graded_connection_curvature_bianchi`) with the Hodge
instanton equations, eliminating any external Bianchi hypothesis.
The duality order is strictly verified by `euclidean_vs_lorentzian_hodge_square_duality`
(from `Algebra/HodgeStarSignatureFour.lean`): Euclidean 2-form Hodge duality gives
a genuine idempotent split Peirce decomposition (`P±² = P±`, `P+ + P- = 1`),
whereas Lorentzian 2-form Hodge duality squares to `-1`. Peirce parity
(`parityConj P`, `PeirceDefectBridge`) and Hodge duality (`matrixHodgeStar star`)
remain on distinct carriers with no unproved conflation between them.

### Phase 0 inventory (archetype → owner → carrier)

- Peirce grading derivation / MC curvature / self-duality:
  `OperatorAlgebra/PeirceDefectBridge.lean:138-200`, carrier ring `B`, `P²=P`.
- Two-sheet inductive colimit cone:
  `Canonical/TwoSheetedYangMillsInductiveColimit.lean:332-402`,
  `InductiveStarColimitCone {stepHom, toColimit, compat}`; concrete `TowerLevel → TowerColimit`.
- Stage → bondMap → ofStage → Limit:
  `Canonical/PeirceTetraktysColimitCoercivity.lean:92-157`, `Stage n` / `Limit`.
- Matrix connection carrier:
  `Canonical/SelfDualConnectionCurvatureYangMillsBridge.lean`, carrier
  `Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)`, `curvatureFromConnection d A = dA + A*A`,
  `covariantDerivative A d M = dM + [A,M]`.
- Bianchi `D_A F_A = 0`:
  `Canonical/CurvatureFromConnectionBianchiBridge.lean:54-69`, derived from `d²A=0`
  + `d(A*A)=dA*A - A*dA` (explicit premises).
- Structural `d²` / graded Leibniz:
  `Canonical/ExteriorGradedDerivationBridge.lean:23`, `Canonical/GradedConnectionBianchiBridge.lean`.
- Matrix curvature transport lane:
  `Canonical/MatrixConnectionCurvatureTransport.lean`, ring homs with explicit
  `matrixExteriorDerivative` compatibility; **no `Stage n → Mat` map asserted**.
- Hodge ★ / self-dual defs:
  `Canonical/YangMillsSelfDualInstantonBridge.lean:34-62`, `matrixHodgeStar`,
  `isSelfDualCurvature`, `isAntiSelfDualCurvature`, `self_dual_solves_yang_mills`.
- Hodge axioms + instanton composition:
  `Canonical/HodgeStarYangMillsSelfDuality.lean` (new).
- Peirce-to-matrix carrier map:
  `Canonical/PeirceToMatrixConnectionCarrierMap.lean` (new). Ring hom `f : Mat →+* Mat`
  preserving idempotents; intertwines `genPhi`, `genV`, `peirceGradingDeriv`,
  `peirceCovariantDeriv`, `peirceMaurerCartanCurvature`; transports curvature,
  covariant derivative, and Bianchi via `MatrixConnectionCurvatureTransport`
  under explicit differential-compatibility hypotheses.

Phase 4 (Peirce-to-connection edge) — complete. `PeirceToMatrixConnectionCarrierMap`
defines a carrier map `f : Mat →+* Mat` (ring hom preserving idempotents), proves
intertwining of all Peirce operations (`genPhi`, `genV`, `peirceGradingDeriv`,
`peirceCovariantDeriv`, `peirceMaurerCartanCurvature`), and uses
`MatrixConnectionCurvatureTransport` for curvature/covariant-derivative/Bianchi
transport under explicit differential-compatibility hypotheses. The identity map
is provided as a concrete carrier map (`identity_is_carrierMap`).

### Gap (remaining phases)

Phase 3 (trace/topological archetypes) — partially done on the finite
exterior-form carrier. `ExteriorEvenTraceChernWeil` proves degree-restricted
trace cyclicity for `A * (F * F)` when `F` is homogeneous of degree two, proves
`Tr(D_A(F²)) = d Tr(F²)` without a blanket cyclicity premise, and derives
closedness of the traced curvature square from graded Bianchi. Its
`connection_curvature_square_class_exact_invariance` theorem then proves that
the resulting de Rham class is unchanged by adding an exact form, using the
existing quotient owner. The actual Chern–Simons transgression identity and
the broader trace-class/Fredholm-determinant/spectral-zeta connections to finite
stages remain open.

The current concrete Phase 3 step adds matrix-level graded trace cyclicity for
homogeneous degrees 1 and 3, and proves `Tr(A⁴)=0` for a homogeneous
matrix-valued 1-form under explicit characteristic-zero and torsion-free scalar
action assumptions.

Update (kernel-checked transgression): the genuine transgression identity is
now proved in `Canonical/ChernSimonsTransgressionKernel.lean`
(`transgression_kernel`): with explicit hypotheses `d²=0`, graded derivation,
`A` homogeneous one-form, `dA` homogeneous two-form, `[CharZero R]`, and
torsion-free scalar action, it derives

`d Tr(A·dA + (2/3)•A³) = Tr((dA + A²)·(dA + A²))`

from the graded Leibniz law (`matrixExteriorDerivative_one_form_mul_derivative`,
`..._one_form_cube_of_graded`), the degree-restricted graded trace cyclicities
(`matrix_trace_one_three_anticommute`, `matrix_trace_even_cyclic`), and the
degree-four trace vanishing `Tr(A⁴)=0` — no blanket cyclicity premise, and the
`(2/3)` scalar is justified by `field_simp` under `[CharZero R]`. The carrier definitions of the transgression lane (`chernSimonsDensityForm`,
`curvatureFromConnection`) stay in
`Canonical/ChernSimonsTransgressionInstantonBridge`, which is now a
definitions-only file: the former duplicate theorem
`chern_simons_transgression_derivation` there is retired (it had zero external
dependents; a kernel-checked copy lives in the correct-coefficient bridge), and
an attempt to import the kernel from that file was removed after lake reported
a build cycle through `EvenTrace → GradedConnectionBianchi →
CurvatureFromConnectionBianchi → ChernSimonsTransgressionInstantonBridge`.
The single public transgression theorem
`Canonical/ChernSimonsCorrectCoefficientTransgressionBridge.chern_simons_transgression_derivation`
carries the explicit `h_dA` degree hypothesis (the graded-derivation interface
owns no degree-raising lemma — verified by repo-wide search) and delegates to
the kernel, so the density/curvature row has exactly one proof body. The remaining Phase 3 open
item is the broader trace-class/Fredholm-determinant/spectral-zeta connection
to finite stages.

Phase 5 (finite-lattice archetypes) — survey done, instantiation row open.
Deep search (2026-11-03) shows the generic Wilson-loop / causal-flow lens
already exists (`Topology/WilsonLoopThermodynamics` `LoopWord`/`holonomy`/
`flowHolonomy`, `Topology/BostConnesWilsonLoop` `curvatureReadout` with
`curvatureReadout_eq_zero_of_detailed_balance`, and
`Topology/ThermodynamicGauge.CausalNonequilibriumFlow` with the
detailed-balance characteristic), quantified over any ring `Op`, and the
staged exact-connection owner `Canonical/TensorStageExactConnection` owns
`exactCutCurvature` with its `stageEmbed`/`bondMap` transports. The open row
is the finite-stage instantiation: `Op := Stage n`, a detailed-balance cut
flow from the staged idempotent corner, and the plaquette curvature-collapse
discharged by the owned generic lemma. Ground-truth contract:
`handover/injections/finite-stage-plaquette-wilson-contract.md`; designated
owner file `lean/InfoGeometry/Canonical/FiniteStagePlaquetteWilson.lean`.

Phase 6 (finite QFT and spectral-gap archetypes) — not started. No mass-gap,
KMS, or finite-temperature owner connects to the finite-stage carriers.

Phase 7 (finite-stage-to-inductive-colimit edges) — done on the finite
carrier. `MatrixToColimitEdge`
defines the carrier map `gradeZeroMatrixRingHom : Mat →+* Stage N` using entry-wise
grade-zero projection and `Idx N` ↔ `Fin (2^N)` reindexing via `idxEquivFinPowTwo`,
composed with `ofStage N : Stage N →+* Limit`. `map_add'`, `map_zero'`, `map_one'`, and
`map_mul'` are all proved: the `map_mul'` proof closes with the reindexing sum
transfer `Equiv.sum_comp (idxEquivFinPowTwo N)` over the `Fin (2^N) /
Finset.univ` product expansion, closing the former `AddHom.map_sum` /
`Finset.sum_bij` typeclass-inference blocker of the Lean 4.34.1 era.
`matrixToColimitRingHom = (ofStage N).comp gradeZeroMatrixRingHom` is defined
and no longer carries an open `sorry`; the downstream statements that depended
on `map_mul'` (colimit-level curvature composition) are unblocked on this edge.

`TensorStageExactConnection` proves `bondMap_exactCovariantDerivative` and
`bondMap_exactCutCurvature`, while `TensorStageFrechetConnection` transports
the finite-stage Fréchet–Leibniz covariant action. `TensorLimitExactConnection`
proves the CE curvature/Bianchi results on `Limit`. These remain the tensor tower's
CE/Fréchet lane: no proved edge connects the matrix exterior-form carrier into
the colimit cone.

For each remaining gap, the plan's verification gates apply: build the owner
module under the locked build workflow, prove one substantive theorem at a time,
and only then connect consumers.

## Poset verification gates

For each archetype or poset edge, prove one substantive theorem at a time:

1. Build the exact owner module with the repository's locked, sequential build
   workflow after checking no compiler task is already running.
2. Run applicable proof-proxy, semantic-vacuity, no-placeholder, and axiom
   checks. Permit only the standard foundational Lean axioms.
3. Inspect theorem signatures and proof bodies against the Ground-Truth
   Contract; successful compilation certifies only the proposition Lean was
   given.
4. Update consumer imports and theorem references only after the replacement
   archetype is proved; retain import-only facades only when they serve an
   actual module interface.
5. Do not promote an algebraic identity to a topological, physical, or
   Millennium-problem result without the matching carrier and theorem.

## Completion criteria

- All nodes and causal edges of the target archetype poset have explicit
  mathematical statements and focused owner modules.
- Reusable lemmas reside in those owner modules and have full kernel-checked
  proofs, no `sorry`/`admit`/custom axioms, and no assumption-bundling wrappers
  presented as archetypes.
- The poset begins with finite-stage carriers and reaches only the existing
  inductive colimit through proved bonding-map compatibility and descent.
- Every bridge states and proves compatibility of its source and target
  carriers.
- Peirce parity, matrix Hodge duality, lattice plaquette curvature, modular
  flow, and finite spectral-gap archetypes remain distinct unless an explicit
  theorem connects them.
- Any claims outside the finite stages and their inductive colimit are kept out
  of scope unless the repository contains the relevant carrier and a proved
  theorem connecting it.

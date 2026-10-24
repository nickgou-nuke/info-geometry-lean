# Five-stream native integration — verification receipt

## Source changes

- `Canonical/FiveStreamNativeTransport.lean`: 10 theorems, one unit definition.
- `Canonical/Cl11FiveStreamColimitTransport.lean`: four theorems, one group
  representation definition.
- `Canonical/All.lean`: imports the colimit transport owner, hence both new
  owners and all five canonical stream owners are reachable from the umbrella.

All Lean paths above are relative to `lean/InfoGeometry/`. Existing five-stream
owners, PR #205/#206 core owners, and the concurrent master intertwiner were
not rewritten by this task. New proofs have short atomic bodies; no new
certificate/claim-bundling structure was introduced.

## Actual integration edges

| Source | Native consumer and proved connection |
|---|---|
| Stream 1 + Stream 5 | `phaseRotorUnit` gives an actual ambient unit; the moving pole lies in the existing unit orbit and has a preimage under Mathlib's stabilizer-quotient equivalence. |
| Stream 2 + Stream 5 + PR #206 | The quarter-turn unit equals the image of `PresentedGroup.of false` under the existing `ParabolicModularRepresentation.representation`, using the Stream 2 factorization. |
| Stream 4 + PR #206 | The displayed double-shear cube equals the square of the represented quarter-turn unit. |
| Stream 3 + Stream 5 | The conjugated density is the squared-weight sum of moving poles; native `TracialFunctional` weighted readouts obey joint density/observable covariance. |
| Stream 5 + operator infinitesimals | Exact dual-number conjugation identifies the moving-pole tangent coefficient as `-(d+B)`, using the previously verified `Core.InnerConjugationJet`. |
| CAR owners | The existing `SplitClifford.CARPair` and `RealCARPair` interfaces supply the four seed relations without additional inverse assumptions. |
| Cl(1,1) tower | Actual `ofStageAlgHom` sends finite Jordan–Wigner rotors and moving poles to those built from the existing algebraic-limit CAR pair. |
| Algebraic colimit + modular group | `algebraicModularRepresentation k` is an actual homomorphism into units of the existing `Cl11TensorTowerLimit.Limit`; its first generator is the stage image of the finite quarter turn. |

The quotient is the orbit of the chosen pole, not the set of all idempotents
or a new global Grassmannian. Tracial covariance is not a positivity/KMS-state
construction. The circle law is algebraic; no time parametrization or analytic
continuation was introduced. The colimit carrier and maps are reused, not
substituted by a finite surrogate. No faithfulness theorem is asserted.

## Verification evidence

- Five-owner baseline: PASS (`/tmp/five-stream-owners-baseline.log`).
- New colimit-owner build: PASS, **9,395 jobs**
  (`/tmp/five-stream-native3.log`).
- `InfoGeometry.All` plus all five companion audit modules: PASS,
  **27,062 jobs** (`/tmp/five-stream-native-integrated.log`).
- Strict kernel replay and public transitive axiom collection: **1,067
  declarations across 14 owners**, all PASS (`/tmp/five-stream-native-axioms.log`).
- Allowed axioms only: `propext`, `Classical.choice`, `Quot.sound`.
- New owners: zero compiler warnings and empty forbidden-token scans.
- Staged-source proxy checks on both new owners: PASS, stable index
  (`/tmp/five-stream-native-source-gate.log`). This is not a gate verdict on
  every unrelated concurrent staged file.
- Selected source/olean freshness checks passed; source hashes were unchanged
  before and after replay and at final readback.
- Builds/replays were serialized with the shared build lock and compiler
  process prechecks. No cache deletion, process termination, branch change or
  dependency-pin update occurred.

| Replayed owner | Generated declarations |
|---|---:|
| GrassmannianBundleCyclotomicOrientability | 193 |
| RootsOfZeroUnityMoebiusModularG22 | 187 |
| UnifiedGeometryOperatorSignificance | 184 |
| ModularParabolicCyclotomicSynthesis | 148 |
| DeBruijnRotorAlternationCycle | 137 |
| FiveStreamNativeTransport | 26 |
| Cl11FiveStreamColimitTransport | 12 |
| Cl11CARFockColimitBridge | 19 |
| Cl11TensorInductiveLimit | 13 |
| IdempotentOrbitContracts | 22 |
| ReflexiveNilpotentFlows | 54 |
| OperatorAlgebra/TracialCARDensity | 41 |
| Core/ParabolicModularRepresentation | 24 |
| Core/InnerConjugationJet | 7 |
| **Total** | **1,067** |

The five companion modules contain **111/91/107/67/64 = 440** `#print axioms`
commands. These differ from generated declaration counts; the first reported
count of 112 does not match this source snapshot. A-A/QA-A conversation links
were not independently accessible, so this receipt does not assert their
Gate 0–4 acceptance or a repository-wide zero-warning/zero-trap result.
Existing dependency/root warnings remain.

## Concurrent work and provenance

The newly discovered `FiveStreamMasterIntertwiner.lean` failed the first
baseline with owner-level rewrite/elaboration errors
(`/tmp/five-stream-native-baseline.log`). It was left untouched. The final
transport path does not import it and does not depend on its completion.
That is historical baseline evidence, not a claim about any later repair by
its author. Existing cross-stream identities were not recreated in a second
master packet.

Full source binding for the five owners, companions, new owners and selected
native dependencies: `/tmp/five-stream-native-hashes.json`.
The two new owners contribute **38** generated declarations; no existing
owner implementation is attributed as new work. Changes are staged, not
committed. Source drift outside the selected snapshot is not certified here.

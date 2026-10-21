# Fréchet–Leibniz–Onsager `N`-Operator Goal

## Objective

Develop kernel-checked theorems that connect the repository's actual continuous
Fréchet derivations, finite families of operator-valued forms, derivation-based
Chevalley–Eilenberg (CE) calculus, and finite BKM/Onsager response. The final
result must be a chain of explicit maps and proved compatibility lemmas on the
actual carriers. It must not identify carriers by terminology, degree, graph
proximity, or prose.

“`N`-operator” is not to be used as though it already meant an endomorphism of
an `N`-dimensional space. The existing `NOperatorForm n` is a `Fin n`-indexed
family of `OperatorOneForm`s. Its pointwise functions are not automatically
linear one-forms. The goal must state which of these meanings is used in each
theorem and prove every required linearity property.

## Ground-truth carriers and existing proved owners

- `Canonical/OperatorFrechetForms.lean`: `OperatorFrechetJet E F n` is
  `E → ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F`, and
  `operatorFrechetJet n f` is `iteratedFDeriv ℂ n f`. The same file defines
  `OperatorFrechetForm` using continuous alternating maps. A jet and an
  alternating form are distinct carriers; no conversion is supplied there.
- `Optics/OperatorDerivationForms.lean`: `FrechetOperatorDerivation 𝕜 A`
  consists of a continuous linear map and the noncommutative product rule.
  The file proves its derivative-at-every-point result, commutator closure,
  the `NCDerivation` adapter, and `toDerivationDifferentialSystem` under its
  stated bracket-action identity. It also defines
  `NOperatorForm n := Fin n → OperatorOneForm ...`; the components have no
  linearity field. It already proves `FrechetOperatorDerivation.map_curvature`
  and the pointwise `applyDerivationField_curvature`; do not duplicate these
  product-rule curvature results. `NOperatorForm` has no use in tracked Lean
  outside its declaration.
- `NCG/DerivationDifferential.lean` and
  `OperatorAlgebra/DerivationDifferentialForms.lean`: the repository has
  derivation-indexed alternating form carriers and proved low-degree CE,
  curvature, covariant-Leibniz, and Bianchi results. Do not claim a generic
  all-degree CE differential from an all-degree carrier alone. The commented
  `LinearCESystem` block is not an active declaration.
- `Canonical/NoncommutativeGibbsBKMHessianBridge.lean` and its imported owners:
  in the finite operator algebra, a real second-variation readout of the
  additive Gibbs log-partition is identified with centered BKM covariance and
  a centered `OnsagerTwoOperatorForm`; a two-direction one-form pullback is
  already proved. These are finite, second-order statements with their actual
  Gibbs hypotheses, not a theorem for arbitrary jet order or a CE cochain.
- `Thermo/SouriauOnsagerBKMOperatorForms.lean` proves symmetry and diagonal
  nonnegativity for the BKM one-form readout and skewness for an alternating
  two-form probe. `Thermo/OnsagerDifferentialFormsBridge.lean` proves
  corresponding results for an abstract `OnsagerCasimirSystem` pulled back to
  operator one-forms. Neither file identifies the Gibbs BKM form with a
  CE differential or with arbitrary Fréchet jets.
- `Thermo/BipolarBKMOperatorConnectionReadout.lean` already supplies a
  concrete finite connection, proves its coordinate wedge is the operator
  commutator, and proves symmetric/nonnegative BKM and alternating curvature
  probe readouts. This covers a concrete tangent-space curvature/BKM
  separation; it does not use the derivation CE carrier or generic
  Fréchet-jet API.
- `Thermo/OnsagerOperatorClosure.lean` proves consequences of supplied
  symmetry, skewness, and positivity fields. Any concrete use in this goal
  must construct the forms from existing proved owners and prove those
  properties; restating them as input fields is not closure.

## Source-confirmed gaps to close

1. **Jet/derivation boundary.** The generic iterated-jet API has no proved
   theorem in its owner identifying the first jet of a continuous linear
   derivation with its derivative map or transporting the Leibniz identity to
   that first-jet readout. (A separate `HasFDerivAt` theorem exists in the
   derivation owner, but it does not mention `operatorFrechetJet`.) Establish
   only statements whose exact domains,
   scalar fields, and evaluation conventions match `iteratedFDeriv`. Do not
   call a higher Fréchet derivative a derivation: higher product derivatives
   have multi-slot product-rule terms, and higher jets are not generally
   alternating.
2. **`NOperatorForm` boundary.** Prove the needed linearity of a chosen
   `OperatorOneForm` before converting it to `Op1Form`; do not coerce an
   arbitrary `Point → Tangent → Value` function into a linear form. For a
   finite family, state componentwise theorems or prove an actual finite-sum
   theorem; do not use an `N`-indexed bundle as an evidence receipt.
3. **Fréchet derivation to CE.** Use the existing adapter and CE owners.
   Where the target needs a Lie algebra/module or a degree beyond the existing
   low-degree operators, construct the actual instance/map and prove its laws.
   The adapter's bracket-action condition is a genuine hypothesis for a
   general family, not a theorem that arbitrary derivations satisfy it.
4. **CE/BKM/Onsager junction.** Give an explicit map from the chosen CE
   derivation directions and coefficient outputs to the finite Gibbs
   perturbation/statistic carriers. Prove the needed compatibility, then
   apply the existing centered Hessian/BKM and Onsager readout lemmas. Do not
   identify a symmetric Hessian with an alternating CE form. A candidate
   consumer-minimal route is to scalarize an actual CE two-cochain by the BKM
   bilinear form and a fixed operator probe, then define a dissipative
   pullback from an actual CE one-cochain; prove all carrier maps, linearity,
   symmetry, skewness, and positivity rather than supplying them as property
   fields. Any curvature contribution must use an actual alternating
   curvature form and a proved probe readout; skewness alone does not prove
   non-vanishing.
5. **Concrete Onsager closure.** If the final theorem uses
   `OnsagerCasimirSystem`, define its dissipative/reversible bilinear maps
   from the concrete BKM and curvature readouts and prove symmetry,
   skewness, and diagonal nonnegativity. Do not set the reversible part to
   zero when claiming a curvature-integrated result, and do not claim it is
   nonzero without a separately proved example.

The source search and DAG establish candidate dependency corridors only. The
exact formulas for items 1–5 must be chosen from inspected owner types and
proved; no declaration is accepted merely because it fills a graph edge.

## AST/AQL and causal-DAG investigation

Following `docs/ASTAQLHASH-HOWTO.md`, source search preceded graph traversal;
all graph operations for this inventory were read-only, and no generation
refresh was performed.

- The recorded query against `http://127.0.0.1:8530`, database `infogeometry`,
  collections `decls`/`edges`, found 775 declaration names containing
  “onsager” across 44 Lean modules. The graph held 171,308 declaration records
  and 1,145,270 edges. All 44 apex modules mapped to tracked Lean owner files.
- The recorded all-apex traversal used depth 3 and a cap of 25 per apex per
  direction: 7,445 backward/prerequisite rows and 3,391 forward/dependent
  rows; two apices had no incident edges. The cap was reached by 133 backward
  and 54 forward cones. Across apices, the traversal returned 1,053 unique
  backward nodes and 1,054 unique forward nodes; these are bounded graph
  results, not semantic groups.
- The shared high-frequency nodes include generic Krein instances and
  doubled-space declarations. Their frequency is navigation information, not
  evidence that those declarations supply Onsager mathematics.
- A focused five-apex depth-4 cross-section of the Gibbs Hessian, CE Bianchi,
  CE covariant-Leibniz, Onsager entropy, and BKM skew-probe owners returned 111
  backward and 6 forward rows; no cap was reached. It showed CE-local
  prerequisites shared between the two CE apices, while the selected Gibbs/BKM
  and CE apices had no common prerequisite in that bounded cone. This does not
  prove source-level disconnection.
- A focused depth-6 cross-section of those same five apices, capped at 1,000
  nodes per direction per apex, returned 146 backward rows and 6 forward rows;
  neither direction reached its cap. It retained 12 shared prerequisites,
  all shared only between the two CE curvature/Leibniz apices (including
  `DerivationLieLane`, `operatorAction_leibniz`, and the CE one-form carrier).
  There were no shared prerequisites across the selected Gibbs/BKM/Onsager
  apices and either CE apex, and no shared consequences. The packet is
  `/tmp/onsager_depth6_core.json`. This is a deeper navigation
  cross-section—not proof that no source-level map exists.
- In that packet, the Onsager entropy apex reaches
  `OnsagerFormsBridge.totalGenerator1Form_nonneg` at depth 1; the CE Bianchi
  apex reaches its canonical Zorn specialization at depth 1; and the BKM probe
  apex reaches the concrete bipolar curvature readout and its separation
  theorem at depths 1–2. The Gibbs-Hessian apex has no forward dependent in
  this query. These paths confirm separate consumer corridors, not a composed
  Fréchet/CE/BKM theorem.
- A separate helper attempt failed during its unresolved-name diagnostic
  because the live graph lacks the optional `syntax_decls` collection. The
  successful depth-6 rerun used the five names already resolved in the
  depth-4 packet. Do not infer a theorem gap from the failed diagnostic.
- `decl_graph_generations` is absent. Graph freshness and source/olean
  correspondence are therefore unknown. Do not refresh the graph without
  explicit authorization: the legacy refresh path can truncate live data.
- Navigation artifacts recorded outside the repository:
  `/tmp/onsager-causal-cones/index.json`,
  `/tmp/onsager-causal-cones/apex-declarations.json`,
  `/tmp/onsager-inventory.md`, `/tmp/onsager_all_apex_cones.json`, and
  `/tmp/onsager_core_cones.json`, `/tmp/onsager_depth6_core.json`. These are
  not theorem evidence and are not repository deliverables.

## Required implementation and acceptance

- Before each source change, repeat exact-symbol and import/dependent searches
  against the current checkout; inspect all candidate owners and preserve
  unrelated staged work.
- Implement the smallest complete chain that reaches the stated objective,
  not a prose packet, an assumed-property structure, a renamed theorem, a
  zero-reversible shortcut, or a scalar/matrix surrogate for a noncommutative
  operator carrier.
- Every mathematical claim must be an actual Lean lemma/theorem with a full
  proof term. No `sorry`, `admit`, authored axiom, `True` wrapper, or
  assumption-wrapped “evidence”/“witness”/“data” declaration is accepted as
  mathematical closure. Genuine mathematical hypotheses on an actual theorem
  are allowed only when stated in that theorem and required by its proof.
- Reuse existing owner declarations rather than duplicating the BKM Hessian,
  derivation adapter, CE differential, Onsager decomposition, or BKM readouts.
- Keep the source modular and downstream-usable. Update imports/aggregators
  only when a real consumer requires them.
- Follow OpenGauss Gate 0–4: ground-truth theorem contract, strict T1–T17
  screening, exact-source A-A review, serial locked Lean verification and
  axiom/vacuity checks, then distinct QA-A rerunning decisive checks. The G-A
  author cannot audit or accept its own change.
- Inspect active compiler processes before any compilation; build sequentially
  through `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock`.
  Never run `lake clean` or remove build caches. Stage edits immediately as
  required by `AGENTS.md`, without changing the existing staged test edit.

## Completion condition

This goal is complete only when the requested Fréchet/Leibniz, `N`-operator,
CE, and finite BKM/Onsager layers are connected by explicit well-typed maps
and kernel-checked compatibility theorems on their real carriers, the concrete
Onsager conclusions are proved rather than assumed, the mathematical scope
does not conflate symmetric jets with alternating forms, and all independent
OpenGauss audit/acceptance gates pass. The current inventory is not completion
evidence.

## Implementation progress (partial; goal remains open)

### Ground-truth contract: Fréchet derivations into the algebraic CE lane

- **Claim:** For a normed real algebra `A`, each `FrechetOperatorDerivation ℝ A`
  determines an element of the existing Lie subalgebra of real-linear Leibniz
  endomorphisms. The map preserves the existing commutator, and evaluation of
  the CE degree-zero differential of the identity-action lane at that image
  equals evaluation of the original Fréchet derivation.
- **Carriers:** Source is the structure
  `FrechetOperatorDerivation ℝ A` (continuous linear map plus Leibniz law).
  Target is `NonAssocDerivation.derivations ℝ A`; the lane direction type is
  that same subalgebra, and the CE one-form is Mathlib's linear one-cochain on
  those directions. The lane includes all algebraic real-linear derivations;
  the Fréchet map is not claimed surjective and no CE equivalence is claimed.
- **Existing owners:** `NonAssocDerivation.derivations` is the Lie subalgebra
  with its inherited commutator (`Algebra/NonAssocDerivation.lean`);
  `DerivationLieLane` requires a Lie hom action into it and a proof of
  faithfulness (`Algebra/DerivationLieLane.lean`);
  `FrechetOperatorDerivation` and its continuous commutator are in
  `Optics/OperatorDerivationForms.lean`; the CE degree-zero differential and
  its evaluation theorem are in
  `OperatorAlgebra/DerivationDifferentialForms.lean`.
- **Gap status:** The recursive search originally found no generic
  identity-action lane or Fréchet adapter. This change closes that narrow gap
  by constructing the identity-action lane and the real-linear Fréchet map,
  with commutator compatibility. The older `NCDerivation` adapter remains a
  separate integer-linear route and is not used as a substitute here.
- **Not established:** This does not make the CE lane continuous-only, prove
  surjectivity, identify arbitrary `NOperatorForm`s with CE cochains, or connect
  the CE calculus to Gibbs/BKM/Onsager response. In particular, unrestricted
  pointwise `OperatorOneForm`s still need actual linearity proofs before any
  linear-form conversion.

The initial `lean/InfoGeometry/Canonical/OperatorFrechetDerivationJet.lean`
change proved
`operatorFrechetJet_one_apply` and `operatorFrechetJet_one_mul`. These identify
the evaluated first iterated Fréchet jet of a complex continuous operator
derivation with its continuous linear representative, and derive the product
specialization from the derivation's Leibniz law. The module also restricts a
complex derivation to the real scalars and proves that its first-jet value is
the coefficient readout of the resulting `NCDerivation`. At that initial
stage, this was only a coefficient-level identification; the later bridge
below adds the Lie-indexed CE connection. All jet claims are order one.

Observed verification for this partial change:

- `python3 tools/infra/opengauss_screener.py lean/InfoGeometry/Canonical/OperatorFrechetDerivationJet.lean lean/InfoGeometry/Canonical/OperatorFrechetDerivationJetAudit.lean --strict` reported 0 traps.
- `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.OperatorFrechetDerivationJet` exited 0 and reported `Build completed successfully (9177 jobs)`.
- `python3 tools/infra/opengauss_cli.py certify --file lean/InfoGeometry/Canonical/OperatorFrechetDerivationJet.lean --write-audit --verify-kernel` exited 0, wrote the companion audit for five declarations, and reported `Kernel verification: passed` and `Axiom audit passed`.

The initial Lean source and its progress-ledger revision passed source-only
A-A review. A distinct QA-A reran the strict screen, locked module build, and
kernel-backed axiom certification for that earlier version, returning
`ACCEPTED_WITH_LIMITED_SCOPE`. QA-A did not regenerate the companion audit
file; the recorded Gate 4 run above did. These checks do not close the full
objective. The later `CEOneFormNOperatorBridge` sections record the proved
`NOperatorForm`/linear one-form carrier map and the CE-to-finite-Gibbs/BKM
Hessian junction. Remaining work is concrete Onsager symmetry and positivity
on this CE-derived carrier, together with a curvature-derived reversible
term and its compatibility/nontriviality results.

### Subsequent Fréchet-to-CE bridge progress

`OperatorFrechetDerivationJet.lean` now also defines the identity-action lane
on the full real-linear Leibniz Lie subalgebra and maps each continuous real
Fréchet derivation into its direction carrier. The module proves preservation
of the commutator. It further identifies the evaluated first Fréchet jet of a
complex derivation with the CE degree-zero differential evaluated on the
real-restricted derivation direction. This is an explicit first-jet-to-CE
evaluation theorem, not an equivalence of CE complexes; the lane still
contains all algebraic derivations, not only continuous ones.

For the bridge revision before the combined first-jet theorem, the locked
module build and generated axiom audit passed. The strict T1–T17 screener
reported zero traps, the no-hypothesis gate passed, and semantic-vacuity
screening found only the pre-existing `restrictScalarsReal_apply` `rfl`
accessor warning. The independent A-A requested that the trivial standalone
CE evaluation readback be replaced by a theorem combining it with the first
jet. That correction was made and the final A-A returned `PASS`. A distinct
QA-A reran the strict screener, no-hypothesis gate, semantic-vacuity scan,
locked module build, Gate 4 kernel review, and axiom certification, returning
`ACCEPTED_WITH_LIMITED_SCOPE`. The QA-A scan reported only the same
`restrictScalarsReal_apply` accessor warning. This partial result does not
close the overall goal.

### Implemented theorem contract: finite CE families in the `NOperatorForm` carrier

This bridge is restricted to CE one-cochains, whose native carrier supplies
real linearity. For a real derivation lane `K` acting on a real algebra `A`,
and a family `ω : Fin n → OneForm K`, `ofCEFamily` constructs an
`NOperatorForm n` with point carrier `Unit`, tangent carrier `K.L`, and value
carrier `A`. `component` proves the value at `()` is an actual
`Op1Form ℝ K.L A` by deriving additivity and real homogeneity from the CE
cochain. The first-jet compatibility theorem uses the normed complex-algebra
assumptions required by the existing Fréchet owner; no finite-dimensionality
claim is part of this generic family encoding. There is no total conversion
from arbitrary `NOperatorForm`s:
those are unrestricted functions, so linearity is absent.

The Fréchet/CE compatibility theorem for a singleton CE family identifies
evaluation of its extracted `Op1Form` at the real derivation direction with
`operatorFrechetJet_one_apply`; the existing combined
jet-to-`exteriorDerivativeZero` theorem supplies the mathematical equality.
`singletonCE_gibbsHessian_chain` extends this chain to the finite Gibbs/BKM
readout, preserving the existing one-sided self-adjointness hypothesis on
the first perturbation. The bridge does not assert swapped-direction
symmetry, a constitutive law, Onsager positivity, or a reversible curvature
contribution; those require separately proved results.

`Canonical/CEOneFormNOperatorBridge.lean` now implements this carrier step:
`ofCEFamily` embeds a finite CE family into `NOperatorForm`, and `component`
constructs an `Op1Form` by evaluating that encoded function and proving its
additivity and real homogeneity from the CE cochain. The singleton first-jet
theorem states the explicit chain from evaluation of `ofCEFamily`, through
evaluation of the extracted `Op1Form`, to the first Fréchet jet at the
real-restricted derivation direction. Its Fréchet-specific assumptions are
the normed complex-algebra assumptions of the existing Fréchet owner; no
finite-dimensionality is asserted here. The target module build and Gate 4
kernel/axiom audit passed for the final theorem-statement revision. A distinct
QA-A reran the strict staged screen, no-hypothesis gate, semantic-vacuity
gate, target locked build, and staged diff check. A-A and QA-A accepted the
revised chain. Strict screening and the no-hypothesis gate passed;
semantic-vacuity screening flags the single `component_apply` `rfl` readout
theorem as a trivial-surface warning. Earlier independent reviews caught and
prompted correction of a bypass in the singleton conclusion; both the
current A-A and QA-A accept the revised conjunction. The goal scope was
corrected to avoid claiming finite-dimensionality for the generic family
map. The finite Gibbs/BKM theorem and its verification status are recorded
below; the full Onsager goal remains open.

### Implemented theorem: CE-derived finite Gibbs/BKM response

The implementation specializes the above CE family to
`A := NoncommutativeGibbsBKMHessianBridge.Operator n`. For `a : A`, set the
singleton CE family to `exteriorDerivativeZero K a`, where
`K := realDerivationsLane A`; use `component` to obtain the genuine
`Op1Form ℝ K.L A`. For continuous complex Fréchet derivations `D` and `E`,
the two Gibbs Hessian perturbations are the values of this same CE-derived
one-form at `FrechetBridge.toRealDerivation (restrictScalarsReal D)` and the
corresponding direction from `E`.

`singletonCE_gibbsHessian_chain` states the chain (i) encoded `NOperatorForm`
readout equals extracted `Op1Form` readout for `D`, (ii) that readout is the
first Fréchet jet, and (iii) the real additive Gibbs log-partition Hessian
on the two CE readouts equals
`centeredBKMOperatorBilinForm` on the extracted CE one-forms and the two
independent directions. It retains exactly the Gibbs hypotheses of the
owner (`IsSelfAdjoint H`, positive real partition) and the owner’s
one-sided `IsSelfAdjoint` condition on the first CE readout. This theorem
does not assert swapped-direction symmetry or a constitutive law; those need
their own proved hypotheses/results. The target owner already proves the
two-vector Hessian pullback, and exact-name recursive search found no prior
direct CE-family consumer in the current tracked Lean source. The bridge
applies that owner theorem to close the finite CE/BKM junction under its
stated self-adjointness hypothesis.

### Implemented theorem: curvature-derived finite CE Onsager system

`Canonical/CEBKMOnsagerSystem.lean` defines the finite carrier `K.L`, with
`K := realDerivationsLane (GibbsOperator n)`, and constructs the dissipative
form by pulling back the real BKM form after the proved `centeringLinearMap`.
Its readout is the centered BKM covariance on the CE one-form values.
Symmetry follows from `centeredBKMRealCovariance_symm`; diagonal
nonnegativity follows from finite Kubo–Mori self-pairing nonnegativity.
The density operator and its continuous power are inputs; this owner does not
identify that density with a Gibbs state or prove a log-partition Hessian
identity for this system. Its finite BKM covariance is a real bilinear form
for arbitrary operator inputs; no physical covariance interpretation for
non-self-adjoint observables is asserted.

The reversible form fixes `Q` in the second BKM argument and applies the
first argument to the actual CE curvature
`connectionCurvature K (exteriorDerivativeZero K a) x y`. Its bilinearity is
proved by transporting the CE two-cochain's linearity through the fixed-probe
BKM linear map, and skewness follows from `twoCochain_skew`. These forms
populate the actual `OnsagerCasimirSystem`; the entropy theorem proves the
total-generator diagonal equals the centered covariance and is nonnegative.
The reversible readout is not defined as zero. No non-vanishing example or
time-reversal parity reciprocity is claimed.

Verification for this owner: locked target build passed (9,216 jobs); OpenGauss
Gate 2 static review passed with zero sorries/admit/trap violations; strict
T1–T17 screen passed with zero traps; no-hypothesis gate passed; Gate 4 wrote
and kernel-verified an 11-declaration axiom audit. Semantic-vacuity screening
reported one trivial-surface warning for the `rfl` readout theorem
`ceCurvatureBKMProbeForm_apply`. Independent source-only A-A returned PASS
with the scope correction above; distinct QA-A returned
`ACCEPTED_WITH_LIMITED_SCOPE` after rerunning the strict screen,
no-hypothesis gate, semantic-vacuity scan, and staged diff check. QA-A did not
rerun the build or Gate 4; those results are the recorded G-A checks above.

### Implemented theorem: Gibbs Hessian equals CE Onsager dissipation

`Canonical/CEBKMOnsagerGibbsIntegration.lean` specializes the concrete CE
Onsager system to `faithfulGibbsDensity H hH hZ` and its proved continuous
real-power path—the same density and path used by the log-partition Hessian
owner. For two continuous complex Fréchet derivations `D` and `E`, the mixed
real Hessian on the corresponding `finiteCEOperatorForm` values equals the
system's dissipative component. The first CE perturbation alone carries the
existing self-adjointness hypothesis. On the diagonal, the system's actual
total-generator production equals the Gibbs Hessian and is nonnegative. No
off-diagonal total-generator/Hessian equality is asserted; the reversible
term remains curvature-derived and is removed only on the diagonal by its
proved skewness.

The source-bound contract and navigation receipt are
`proofs/FrechetLeibnizOnsagerGibbsIntegration.contract.json` and
`proofs/FrechetLeibnizOnsagerGibbsIntegration.discovery.json`. Contract
validation passed. The target locked build and Gate 4 kernel/axiom audit
passed. Strict T1–T17 screening, Gate 2, semantic-vacuity (zero findings),
staged proof-proxy, and diff checks passed. The repo-wide no-hypothesis scan
cannot currently traverse `.changes/.agents/challenger_2_m1/test_f4.lean`
because that path is a directory; its scoped scan of the target canonical
directory passes. Independent A-A returned PASS. QA-A's checks passed but it
withheld package acceptance until this ledger and the contract distinguished
the now-proved pairwise family results from the still-open family-to-system
identification and aggregate positivity. The original system identity is
finite and for a single CE observable; nonvanishing curvature and
time-reversal parity are not thereby established.

### Next theorem contract: concrete `Fin m` Fréchet/CE family

The finite `Fin m` componentwise bridge is now in
`CEBKMOnsagerGibbsIntegration.lean`: each existing `ofCEFamily` readout equals
the corresponding first Fréchet jet, and each pairwise Hessian equals the
centered BKM form on the extracted `Op1Form`s. It reuses `ofCEFamily` and
`component`; no second `NOperatorForm` or BKM carrier was introduced. The
componentwise first-jet and pairwise family response are established. The
diagonal component Hessian-to-Onsager identifications and the weighted
finite-family quadratic positivity theorem are now proved below. Still open
here is the explicit pairwise double-sum expansion of that aggregate quadratic
in terms of the family response entries; no aggregate matrix representation
or entrywise matrix theorem is claimed.

A separate non-vanishing theorem for the reversible readout is optional only
after a concrete finite derivation pair and BKM probe yield a proof; it cannot
be inferred from skewness. Time-reversal parity reciprocity remains outside
scope unless an actual parity action and its compatibility are constructed.

### Implemented theorem: weighted finite-family BKM quadratic positivity

The owner now proves
`finiteGibbsCEFamily_aggregateBKM_quadratic_nonneg`. For every finite family
`a : Fin m → GibbsOperator n`, real coefficients `c`, and Fréchet-induced
derivation direction, it identifies the operator sum of the weighted CE
readouts with the CE readout of the weighted sum of the original operators.
The equality follows from linearity of the actual derivation action and the
degree-zero CE differential. Applying `centeredCEBKMForm_nonneg` then gives
nonnegativity of the centered BKM covariance of that concrete summed
operator. This is a finite-family quadratic positivity theorem, not a
property-bearing data structure and not an identification of the cross-index
Hessian with one single-observable Onsager system.

Its ground-truth contract and discovery receipt are
`proofs/FrechetLeibnizOnsagerFamilyAggregate.contract.json` and
`proofs/FrechetLeibnizOnsagerFamilyAggregate.discovery.json`; contract
validation passed before the source edit. The target locked build passed after
the final proof correction. The target has existing dependency warnings; the
build is not a warning-free full-repository closure. A-A returned PASS after
correcting stale out-of-scope claims; distinct QA-A returned
`ACCEPTED_WITH_LIMITED_SCOPE`. QA-A independently reran both contracts,
Gate 2, strict T1–T17 screening (zero traps), semantic-vacuity (zero
findings), the scoped no-hypothesis scan, cached diff check, locked target
build, and `certify --verify-kernel` against the existing 10-declaration audit
(no rejected axioms, only standard foundational axioms). Remaining
family-level work was the explicit pairwise double-sum expansion, now recorded
below. The end-to-end objective also still requires completing the exact
Fréchet/Leibniz, `NOperatorForm`, CE, and concrete finite Onsager chain under
its stated domains, plus independent acceptance of each new theorem slice.

### Implemented theorem: pairwise family BKM quadratic expansion

The owner now proves
`finiteGibbsCEFamily_pairwise_quadratic_eq_aggregateBKM`. Its first
conclusion expands the coefficient-weighted aggregate covariance as
`∑ i, c i • ∑ j, c j • Cov_BKM(aᵢ(D), aⱼ(D))`; its second proves that this
pairwise quadratic is nonnegative. The proof uses the already-owned
`quotientBKMForm` on the scalar-gauge quotient, proves the finite quotient-map
sum compatibility needed for the actual CE readouts, expands the bilinear
form in each argument, and returns each quotient entry to the native
`centeredBKMRealCovariance` using `quotientBKMForm_mk`. It reuses the existing
quotient and family carriers; it introduces no response-matrix data wrapper.

The theorem contract and fresh navigation receipt are
`proofs/FrechetLeibnizOnsagerFamilyPairwiseQuadratic.contract.json` and
`proofs/FrechetLeibnizOnsagerFamilyPairwiseQuadratic.discovery.json`.
Contract validation, Gate 2, strict T1–T17 screening, semantic-vacuity,
scoped no-hypothesis, target locked build, and Gate 4 kernel/axiom audit have
passed. The generated audit now covers 11 declarations. A-A returned PASS.
An independent QA-A reran all technical gates, including the locked target
build and kernel verification of the existing audit, then returned
`ACCEPTED_WITH_LIMITED_SCOPE` after a procedural ledger mismatch was corrected.
The
pairwise entries are centered BKM responses;
the already-proved pairwise Hessian theorem identifies them with Gibbs
Hessian entries only under its stated first-perturbation self-adjointness
hypothesis. This result does not identify off-diagonal Hessians with one
single-observable Onsager system or establish infinite-dimensional claims.

### Implemented theorem: pairwise family quadratic equals aggregate Gibbs Onsager response

The owner additionally proves
`finiteGibbsCEFamily_weightedReadout_eq`, the exact finite linearity identity
for the CE readout of a weighted observable sum, and
`finiteGibbsCEFamily_pairwise_quadratic_eq_aggregateOnsagerDissipation_hessian`.
The latter identifies the already-expanded pairwise centered-BKM quadratic
with the dissipative bilinear form of `finiteGibbsCEOnsagerSystem` evaluated
at the weighted aggregate observable. Under self-adjointness of that actual
aggregate CE readout, the same quadratic equals the real second derivative
of the finite Gibbs log-partition; its nonnegativity is proved from the
finite BKM positivity owner. This is one aggregate observable and one
Fréchet-induced direction, not an off-diagonal family-index Onsager theorem.

The source-bound contract and regenerated local discovery receipt are
`proofs/FrechetLeibnizOnsagerFamilyAggregateOnsager.contract.json` and
`proofs/FrechetLeibnizOnsagerFamilyAggregateOnsager.discovery.json`.
Contract validation, target build, Gate 4 kernel/axiom audit (13 declarations,
only standard foundational axioms), strict T1–T17 screening, semantic-vacuity,
scoped no-hypothesis, staged proof-proxy, and cached diff checks pass. The
independent source-level QMS review passed, and a distinct QA-A returned
`ACCEPTED_WITH_LIMITED_SCOPE` after independently rerunning the locked target
build and all listed gates. The audit output contains only standard
foundational axioms. The build emits unrelated dependency/style/deprecation
warnings, so this is not a warning-free full-repository closure. Source hashes
and line ranges in the affected family contracts and their local discovery
receipts were refreshed after the shared owner edit.

### Implemented theorem: independent-direction `NOperatorForm` Gibbs Onsager system

`Canonical/CEBKMOnsagerGibbsNOperatorFamily.lean` closes the product-family
seam with actual operators and full Lean proofs. For `a : Fin m →
GibbsOperator n`, it constructs the CE family using the existing
`ofCEFamily` carrier and extracts each component as an `Op1Form`. The theorem
`finiteGibbsCEFamilyNOperatorComponent_eq_firstFrechetJet` proves the encoded
component readout equals that extracted linear form and the order-one
Fréchet-jet value for each independent component derivation.

The explicit map `finiteGibbsCEFamilyNOperatorReadoutLinear` sends a product
of CE directions to the real weighted sum of component readouts. The
dissipative bilinear form is the centered finite BKM covariance pulled back
along this map. The reversible bilinear form is the weighted sum of the
existing fixed-probe readouts of each component's native CE curvature. The
definition does not assert that the curvature sum equals curvature of the
weighted observable. The concrete `OnsagerCasimirSystem` proves symmetry,
skewness, and nonnegative total diagonal production; the entropy theorem
identifies that production with the BKM covariance of the actual aggregate
readout.

For independent families `D E : Fin m → FrechetOperatorDerivation ℂ ...`,
`finiteGibbsCEFamilyNOperatorPairwiseBKMResponse_eq_aggregateBKM` expands the
weighted pairwise covariance by bilinearity on the scalar-gauge quotient.
`finiteGibbsCEFamilyNOperatorSystem_pairwise_eq_dissipation_hessian` then
identifies it with the product-carrier Onsager dissipation and the real mixed
Gibbs log-partition Hessian. Its only perturbation-side hypothesis is
self-adjointness of the first aggregate readout, exactly as required by the
general finite Hessian owner. This is finite-dimensional and does not claim
parity reciprocity, nonzero reversible response, or a universal
infinite-dimensional/colimit theorem.

The source-bound contract and exact-symbol discovery receipt are
`proofs/FrechetLeibnizOnsagerFamilyNOperatorSystem.contract.json` and
`proofs/FrechetLeibnizOnsagerFamilyNOperatorSystem.discovery.json`. Contract
validation, Gate 2, strict T1–T17 screening, scoped no-hypothesis,
semantic-vacuity (one advisory trivial-readout warning), staged proof-proxy,
and cached diff checks passed. The owner compiled through the shared locked
build (9,218 jobs), and Gate 4 review plus certification kernel-checked all 20
declarations with only `propext`, `Classical.choice`, and `Quot.sound`; no
custom axioms, `sorry`, or `admit` were reported. A-A passed on the exact
staged source after the final proof edits. A distinct QA-A independently
reran contract/receipt validation, strict screens, no-hypothesis and staged
gates, target build, Gate 4, and certification, returning PASS. Existing
LeanCopilot/LeanArchitect local-change warnings remain; this is not a claim
of a warning-free full-repository build.

### Completion audit

The five source-confirmed requirements at the start of this goal are now
covered by kernel-checked owners: the order-one Fréchet-jet/Leibniz and
Fréchet-to-CE adapter remains in `OperatorFrechetDerivationJet.lean`; the
actual `NOperatorForm` to CE-one-form extraction and first-jet compatibility
is used by the new family owner; the independent product-direction family is
mapped to the CE carrier componentwise; the finite quotient-BKM expansion
and general Gibbs Hessian owner are applied on their actual operator
carriers; and the family Onsager dissipation and reversible curvature forms
are constructed with symmetry, skewness, and nonnegative entropy production
proved, not supplied as fields. No symmetric Hessian is identified with an
alternating CE form. The OpenGauss A-A and QA-A gates for the final family
owner passed. This completion statement is limited to the explicit finite
Gibbs, real-coefficient, Fréchet-induced carrier and hypotheses above; the
out-of-scope analytic and parity claims remain unproved.

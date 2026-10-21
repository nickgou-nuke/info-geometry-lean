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
- **Smallest gap:** No generic identity-action lane on the full derivation
  subalgebra, nor an adapter from the Fréchet derivation carrier to it, was
  found in the recursive Lean search. The older `NCDerivation` adapter is
  integer-linear and does not fill this real-linear lane.
- **Not established:** This does not make the CE lane continuous-only, prove
  surjectivity, identify arbitrary `NOperatorForm`s with CE cochains, or connect
  the CE calculus to Gibbs/BKM/Onsager response. In particular, unrestricted
  pointwise `OperatorOneForm`s still need actual linearity proofs before any
  linear-form conversion.

`lean/InfoGeometry/Canonical/OperatorFrechetDerivationJet.lean` now proves
`operatorFrechetJet_one_apply` and `operatorFrechetJet_one_mul`. These identify
the evaluated first iterated Fréchet jet of a complex continuous operator
derivation with its continuous linear representative, and derive the product
specialization from the derivation's Leibniz law. The module also restricts a
complex derivation to the real scalars and proves that its first-jet value is
the coefficient readout of the resulting `NCDerivation`. This is only a
coefficient-level identification: it does not construct a Lie-indexed action,
bracket compatibility, or a CE differential. All jet claims are order one.

Observed verification for this partial change:

- `python3 tools/infra/opengauss_screener.py lean/InfoGeometry/Canonical/OperatorFrechetDerivationJet.lean lean/InfoGeometry/Canonical/OperatorFrechetDerivationJetAudit.lean --strict` reported 0 traps.
- `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.OperatorFrechetDerivationJet` exited 0 and reported `Build completed successfully (9177 jobs)`.
- `python3 tools/infra/opengauss_cli.py certify --file lean/InfoGeometry/Canonical/OperatorFrechetDerivationJet.lean --write-audit --verify-kernel` exited 0, wrote the companion audit for five declarations, and reported `Kernel verification: passed` and `Axiom audit passed`.

The Lean source and this progress-ledger revision passed source-only A-A
review. A distinct QA-A reran the strict screen, locked module build, and
kernel-backed axiom certification, and returned `ACCEPTED_WITH_LIMITED_SCOPE`.
QA-A did not regenerate the companion audit file; the recorded Gate 4 run above
did. These checks do not close the full objective. Remaining work includes
a proved `NOperatorForm`/linear one-form carrier map, a concrete
Fréchet-derivation-to-CE route with its bracket compatibility, and an explicit
CE-to-finite-Gibbs/BKM/Onsager map with proved compatibility and concrete
dissipative/reversible conclusions. Source scouting found that the proposed
CE-cochain Onsager construction still requires a real-linear derivation Lie
lane on the finite operator carrier, plus a map feeding Fréchet/`NOperatorForm`
data into that lane; no such connection was established by the scout.
